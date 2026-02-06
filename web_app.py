import streamlit as st
import requests
import datetime
import re
import os
import time
import unicodedata
import urllib.parse
from thefuzz import fuzz
from dotenv import load_dotenv
# import sqlite3
import json
import pandas as pd
import threading
import uuid
from enum import Enum

# --- Configuration & Setup ---
load_dotenv()
st.set_page_config(page_title="COI CHECK", layout="wide")

# Initialize simple rate limiting
if 'last_search_time' not in st.session_state:
    st.session_state.last_search_time = 0
if 'is_searching' not in st.session_state:
    st.session_state.is_searching = False
if 'history_queue' not in st.session_state:
    st.session_state.history_queue = []
# Preserve user input across reruns
if 'fixed_input' not in st.session_state:
    st.session_state.fixed_input = ""
if 'candidate_input' not in st.session_state:
    st.session_state.candidate_input = ""
    

USER_EMAIL = os.getenv("USER_EMAIL", "your.email@example.com")
NCBI_API_KEY = os.getenv("NCBI_API_KEY", None)
S2_API_KEY = os.getenv("S2_API_KEY", None)
CURRENT_YEAR = datetime.datetime.now().year
START_YEAR = CURRENT_YEAR - 5

HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/107.0.0.0 Safari/537.36'
}

# --- Database & Persistence ---
# --- Database & Persistence Removed ---

# --- Helper Functions (Refactored) ---

def normalize_name(name):
    return re.sub(r'[^a-zA-Z\s,.\u00C0-\u017F]', '', name).strip()

def parse_semicolon_name(name):
    """Parses 'First;Last' or 'First,Last' or 'First Last'.
    
    For both ';' and ',': text BEFORE separator = First Name, text AFTER separator = Last Name.
    """
    if ';' in name:
        parts = name.split(';', 1)
        if len(parts) == 2:
            return parts[0].strip(), parts[1].strip()
    if ',' in name:
        parts = name.split(',', 1)
        if len(parts) == 2:
            return parts[0].strip(), parts[1].strip()
    parts = name.split()
    if len(parts) >= 2:
        return ' '.join(parts[:-1]), parts[-1]
    return '', name

def generate_wos_search_term(given_name, family_name):
    """
    根据给定的名和姓生成 Web of Science (WOS) 检索式变体列表
    """
    if not family_name:
        return []
    
    variants = []
    
    # 处理名部分
    given_tokens = [t for t in given_name.split() if t]
    initials = [t[0] for t in given_tokens if t]
    initials_str = " ".join(initials)
    initials_compact = "".join(initials)
    first_given = given_tokens[0] if given_tokens else ""
    
    # 姓在前名在后
    if given_tokens:
        variants.append(f"AU=({family_name} {given_name})")                # Lane Nancy Catherine
        variants.append(f"AU=({family_name} {initials_str})")             # Lane N C
        variants.append(f"AU=({family_name} {initials_compact})")         # Lane NC
        variants.append(f"AU=({family_name} {first_given})")              # Lane Nancy
        if initials:
            variants.append(f"AU=({family_name} {initials[0]})")          # Lane N
        variants.append(f"AU=({family_name}, {given_name})")              # Lane, Nancy Catherine
    else:
        variants.append(f"AU=({family_name})")
    
    # 名在前姓在后
    if given_tokens:
        variants.append(f"AU=({given_name} {family_name})")               # Nancy Catherine Lane
        variants.append(f"AU=({initials_str} {family_name})")             # N C Lane
        variants.append(f"AU=({initials_compact} {family_name})")         # NC Lane
        variants.append(f"AU=({first_given} {family_name})")              # Nancy Lane
        if initials:
            variants.append(f"AU=({initials[0]} {family_name})")          # N Lane
        variants.append(f"AU=({given_name}, {family_name})")              # Nancy Catherine, Lane
    
    # 去重
    variants = list(dict.fromkeys(variants))
    return variants

def generate_google_scholar_author_search_term(family_name, given_name):
    """
    生成用于Google Scholar的作者检索式变体列表。
    注意：Google Scholar的检索语法非官方且变化较大，此函数基于常见用法。
    """
    variants = set()
    family_name = family_name.strip()
    given_name = given_name.strip()

    # 1. 使用 author: 操作符（非官方支持，但常用）
    # 格式：author:"姓 名" 或 author:"姓 首字母"
    if given_name:
        variants.add(f'author:"{given_name} {family_name}"')
    
    # 提取首字母
    name_parts = given_name.split()
    initials = ''.join([part[0].upper() for part in name_parts if part]) if name_parts else ''
    if initials:
        variants.add(f'author:"{initials} {family_name}"')

    # 2. 简单地将全名作为短语搜索（不加author:）
    if given_name:
        variants.add(f'"{given_name} {family_name}"')
    if initials:
        variants.add(f'"{initials} {family_name}"')

    # 3. 考虑将名中的特殊字符（如é）转换为标准英文字母
    if given_name:
        normalized_given_name = unicodedata.normalize('NFD', given_name).encode('ascii', 'ignore').decode('ascii')
        if normalized_given_name != given_name:
            variants.add(f'author:"{normalized_given_name} {family_name}"')
            variants.add(f'"{normalized_given_name} {family_name}"')

    return list(variants)

# --- API Logic (Refactored to return list of dicts) ---

def get_pmids_for_author(given_name, family_name):
    base_url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
    given_tokens = [t for t in given_name.split() if t]
    initials = [t[0] for t in given_tokens if t]
    
    search_terms = set()
    if given_name:
        search_terms.add(f'"{family_name} {given_name}"[Author]')
        search_terms.add(f'"{given_name} {family_name}"[Author]')
    if initials:
        search_terms.add(f'"{family_name} {"".join(initials)}"[Author]')
        search_terms.add(f'"{family_name} {initials[0]}"[Author]')
        search_terms.add(f'"{initials[0]} {family_name}"[Author]')

    final_search_term = " OR ".join(list(search_terms))
    if not final_search_term:
        final_search_term = f'"{family_name}"[Author]' if family_name else ''
        if not final_search_term: return set()
    
    params = {
        "db": "pubmed", "term": final_search_term,
        "mindate": f"{START_YEAR}/01/01", "maxdate": f"{CURRENT_YEAR}/12/31",
        "datetype": "pdat", "retmode": "json", "retmax": "100",
        "email": USER_EMAIL, "api_key": NCBI_API_KEY
    }
    try:
        response = requests.get(f"{base_url}esearch.fcgi", params=params, headers=HEADERS)
        response.raise_for_status()
        return set(response.json().get("esearchresult", {}).get("idlist", []))
    except:
        return set()

def fetch_pubmed(fixed_given, fixed_family, candidate_given, candidate_family):
    fixed_pmids = get_pmids_for_author(fixed_given, fixed_family)
    if not fixed_pmids: return []
    candidate_pmids = get_pmids_for_author(candidate_given, candidate_family)
    if not candidate_pmids: return []
    
    common_pmids = fixed_pmids.intersection(candidate_pmids)
    if not common_pmids: return []

    results = []
    try:
        base_url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
        ids = ",".join(common_pmids)
        params = {"db": "pubmed", "id": ids, "retmode": "json", "email": USER_EMAIL, "api_key": NCBI_API_KEY}
        response = requests.get(f"{base_url}esummary.fcgi", params=params, headers=HEADERS)
        response.raise_for_status()
        data = response.json()
        
        for pmid, details in data.get("result", {}).items():
            if pmid == "uids": continue
            title = details.get("title", "No Title")
            pub_year = details.get("pubdate", str(START_YEAR)).split(" ")[0]
            doi = ""
            for an_id in details.get("articleids", []):
                if an_id.get("idtype") == "doi":
                    doi = an_id.get('value')
                    break
            results.append({
                "source": "PubMed",
                "title": title,
                "year": pub_year,
                "doi": doi,
                "details": f"PMID: {pmid}"
            })
    except Exception as e:
        st.write(f"PubMed Error: {e}")
    return results

def get_openalex_author_id(given_name, family_name):
    full_name = f"{given_name} {family_name}".strip()
    if not full_name: return None
    url = "https://api.openalex.org/authors?data-version=2"
    try:
        resp = requests.get(url, params={"filter": f"display_name.search:{full_name}", "mailto": USER_EMAIL}, headers=HEADERS)
        resp.raise_for_status()
        data = resp.json()
        if data.get("results"):
            return data["results"][0].get("id").split('/')[-1]
    except:
        pass
    return None

def fetch_openalex(fixed_given, fixed_family, candidate_given, candidate_family):
    fixed_id = get_openalex_author_id(fixed_given, fixed_family)
    candidate_id = get_openalex_author_id(candidate_given, candidate_family)
    if not fixed_id or not candidate_id: return []

    results = []
    try:
        works_url = "https://api.openalex.org/works?data-version=2"
        # Get fixed author works
        params_f = {"filter": f"author.id:{fixed_id},publication_year:>{START_YEAR-1}", "per-page": 100, "mailto": USER_EMAIL}
        resp_f = requests.get(works_url, params=params_f, headers=HEADERS)
        fixed_works = {w["id"]: w for w in resp_f.json().get("results", [])}
        
        if not fixed_works: return []

        # Get candidate works
        params_c = {"filter": f"author.id:{candidate_id},publication_year:>{START_YEAR-1}", "per-page": 100, "mailto": USER_EMAIL}
        resp_c = requests.get(works_url, params=params_c, headers=HEADERS)
        candidate_works = resp_c.json().get("results", [])

        for work in candidate_works:
            if work["id"] in fixed_works:
                doi = work.get("doi", "").replace("https://doi.org/", "")
                results.append({
                    "source": "OpenAlex",
                    "title": work.get("display_name", "No Title"),
                    "year": work.get("publication_year", "N/A"),
                    "doi": doi,
                    "details": f"OpenAlex ID: {work['id']}"
                })
    except Exception as e:
        st.write(f"OpenAlex Error: {e}")
    return results

def fetch_crossref(fixed_given, fixed_family, candidate_given, candidate_family):
    base_url = "https://api.crossref.org/works"
    author_query = f"{fixed_given} {fixed_family}, {candidate_given} {candidate_family}"
    params = {
        "query.author": author_query,
        "filter": f"from-pub-date:{START_YEAR}-01-01",
        "select": "DOI,title,author,published",
        "rows": 50,
        "mailto": USER_EMAIL
    }
    results = []
    try:
        resp = requests.get(base_url, params=params, headers=HEADERS)
        data = resp.json()
        for item in data.get("message", {}).get("items", []):
            authors = item.get("author", [])
            auth_strs = []
            for a in authors:
                auth_strs.append(f"{a.get('given','')} {a.get('family','')}".strip().lower())
                auth_strs.append(f"{a.get('family','')} {a.get('given','')}".strip().lower())
            
            f_names = [f"{fixed_given} {fixed_family}".lower(), f"{fixed_family} {fixed_given}".lower()]
            c_names = [f"{candidate_given} {candidate_family}".lower(), f"{candidate_family} {candidate_given}".lower()]
            
            best_f = max([fuzz.token_set_ratio(f, a) for f in f_names for a in auth_strs] or [0])
            best_c = max([fuzz.token_set_ratio(c, a) for c in c_names for a in auth_strs] or [0])
            
            if best_f >= 85 and best_c >= 85:
                title = item.get("title", ["No Title"])[0]
                pub = item.get("published-print", item.get("published-online", {}))
                year = pub.get("date-parts", [[START_YEAR]])[0][0] if pub else START_YEAR
                results.append({
                    "source": "Crossref",
                    "title": title,
                    "year": year,
                    "doi": item.get("DOI"),
                    "details": f"Match Score: {best_f}/{best_c}"
                })
    except Exception as e:
        # st.write(f"Crossref Error: {e}") 
        pass
    return results

last_s2_time = 0
def s2_safe_request(url, params):
    global last_s2_time
    min_int = 1.1 if S2_API_KEY else 3.1
    elapsed = time.time() - last_s2_time
    if elapsed < min_int: time.sleep(min_int - elapsed)
    last_s2_time = time.time()
    headers = HEADERS.copy()
    if S2_API_KEY: headers["x-api-key"] = S2_API_KEY
    return requests.get(url, params=params, headers=headers)

def fetch_semanticscholar(fixed_given, fixed_family, candidate_given, candidate_family):
    base_url = "https://api.semanticscholar.org/graph/v1/paper/search"
    f_name = f"{fixed_given} {fixed_family}".strip()
    c_name = f"{candidate_given} {candidate_family}".strip()
    params = {
        "query": f'"{f_name}" "{c_name}"',
        "fields": "title,year,externalIds,authors",
        "limit": 50,
        "year": f"{START_YEAR}-"
    }
    results = []
    try:
        resp = s2_safe_request(base_url, params)
        if resp and resp.status_code == 200:
            for paper in resp.json().get('data', []):
                if paper.get('year') and int(paper.get('year')) < START_YEAR: continue
                
                # Check authors fuzzy
                p_auths = [a.get('name','') for a in paper.get('authors', [])]
                best_f = max([fuzz.token_set_ratio(f_name, a) for a in p_auths] or [0])
                best_c = max([fuzz.token_set_ratio(c_name, a) for a in p_auths] or [0])
                
                if best_f >= 72 and best_c >= 72:
                    results.append({
                        "source": "SemanticScholar",
                        "title": paper.get("title"),
                        "year": paper.get("year"),
                        "doi": paper.get("externalIds", {}).get("DOI"),
                        "details": f"Match: {best_f}/{best_c}"
                    })
    except Exception as e:
        st.write(f"SemanticScholar Error: {e}")
        pass
    return results

def fetch_doaj(fixed_given, fixed_family, candidate_given, candidate_family):
    base_url = "https://doaj.org/api/v4/search/articles/"
    # Query syntax: (bibjson.author.name:"Name1" AND bibjson.author.name:"Name2")
    f_name = f"{fixed_given} {fixed_family}".strip()
    c_name = f"{candidate_given} {candidate_family}".strip()
    
    query = f'(bibjson.author.name:"{f_name}" AND bibjson.author.name:"{c_name}")'
    encoded_query = urllib.parse.quote(query)
    final_url = f"{base_url}{encoded_query}"
    
    params = {
        "page": 1,
        "pageSize": 50
    }
    
    results = []
    try:
        resp = requests.get(final_url, params=params, headers=HEADERS)
        if resp.status_code == 200:
            data = resp.json()
            for item in data.get("results", []):
                bib = item.get("bibjson", {})
                
                # Check year filter
                year = bib.get("year")
                if year and int(year) < START_YEAR: continue
                
                title = bib.get("title", "No Title")
                
                # Extract DOI
                doi = ""
                for id_obj in bib.get("identifier", []):
                    if id_obj.get("type") == "doi":
                        doi = id_obj.get("id")
                        break
                
                results.append({
                    "source": "DOAJ",
                    "title": title,
                    "year": year,
                    "doi": doi,
                    "details": "DOAJ Match" 
                })
    except Exception as e:
        st.write(f"DOAJ Error: {e}")
        pass
    return results

def merge_results(all_results):
    merged = {}
    for r in all_results:
        doi = r.get('doi')
        # If no DOI, use title/year slug as key
        if not doi:
            key = f"{r['title'][:30]}_{r['year']}"
        else:
            key = doi.lower().strip()
        
        if key in merged:
            merged[key]["sources"].append(r["source"])
           
            new_pair = r.get("matched_pair")
            if new_pair and new_pair not in merged[key].get("matched_pairs", []):
                if "matched_pairs" not in merged[key]:
                    merged[key]["matched_pairs"] = []
                merged[key]["matched_pairs"].append(new_pair)


            # Preserve Match scores if present in the new result but not in existing

            merged[key]["sources"] = list(set(merged[key]["sources"])) # dedup sources
            
            # Preserve Match scores if present in the new result but not in existing
            new_details = r.get("details", "")
            if "Match" in new_details:
                current_details = merged[key].get("details", "")
                if "Match" not in current_details:
                    merged[key]["details"] = f"{current_details} | {new_details}" if current_details else new_details
                elif new_details not in current_details: 
                     merged[key]["details"] = f"{current_details} | {new_details}"
        else:
            r["sources"] = [r["source"]]
            # --- 修改：在第一次存入时就初始化匹配对列表 ---
            r["matched_pairs"] = [r.get("matched_pair")] if r.get("matched_pair") else []
            # ----------------------------------------
            merged[key] = r
    
    final_list = list(merged.values())
    # Sort by year desc
    final_list.sort(key=lambda x: str(x.get('year', '0')), reverse=True)
    return final_list


# --- Simple Global Lock System ---

class SearchLock:
    """Global lock to prevent concurrent searches with 30s freeze."""
    COOLDOWN_SECONDS = 30
    
    def __init__(self):
        self._lock = threading.Lock()
        self.last_search_finish_time = 0
    
    def get_status(self):
        """
        Returns unified status: (status_code, message)
        status_code: 'ready', 'busy', 'cooldown'
        """
        if self._lock.locked():
            return "busy", "⏳ 系统正在处理其他请求，请稍候..."
        
        elapsed = time.time() - self.last_search_finish_time
        if elapsed < self.COOLDOWN_SECONDS:
            remaining = int(self.COOLDOWN_SECONDS - elapsed)
            return "cooldown", f"❄️ 系统冷却中，请等待 {remaining} 秒后再试"
        
        return "ready", None

    def try_acquire(self):
        status, _ = self.get_status()
        if status != "ready":
            return False
        return self._lock.acquire(blocking=False)
    
    def release(self):
        if self._lock.locked():
            self._lock.release()
            self.last_search_finish_time = time.time()
    
    def force_unlock(self):
        if self._lock.locked():
            try:
                self._lock.release()
            except RuntimeError:
                pass

@st.cache_resource
def get_global_search_lock():
    return SearchLock()

def get_search_lock_safe():
    """Safely get the search lock, handling Streamlit Cloud edge cases."""
    try:
        lock = get_global_search_lock()
        # Verify it's actually a SearchLock instance with expected methods
        if hasattr(lock, 'get_status') and callable(lock.get_status):
            return lock
        else:
            # Invalid cached object, return a new instance
            st.cache_resource.clear()
            return get_global_search_lock()
    except Exception:
        # Fallback: create a fresh instance
        return SearchLock()

search_lock = get_search_lock_safe()

# --- Dialog Function for Detail Display ---

@st.dialog("Detailed Search Results", width="large")
def show_detail_dialog(title, date, result_data):
    """Display detailed search results in a dialog."""
    st.subheader(f"{title}")
    st.caption(f"Search Date: {date}")
    
    # Get data structure
    papers = result_data.get("papers", [])
    search_terms = result_data.get("search_terms", {})
    inputs = result_data.get("inputs", {})
    
    # Show inputs if available
    if inputs:
        with st.expander("Original Input", expanded=False):
            col1, col2 = st.columns(2)
            with col1:
                st.markdown("**Potential COI:**")
                st.code(inputs.get("fixed", "N/A"), language=None)
            with col2:
                st.markdown("**Author(s):**")
                st.code(inputs.get("candidate", "N/A"), language=None)
    
    # Show search terms if available
    if search_terms:
        with st.expander("Generated Search Queries", expanded=False):
            for author_name, terms in search_terms.items():
                st.markdown(f"**{author_name}:**")
                col1, col2 = st.columns(2)
                with col1:
                    st.markdown("*Web of Science:*")
                    st.code(terms.get("wos", "N/A"), language=None)
                with col2:
                    st.markdown("*Google Scholar:*")
                    st.code(terms.get("gs", "N/A"), language=None)
                st.divider()
    
    # Show papers
    st.subheader(f"Found {len(papers)} Potential Collaboration(s)")
    
    if papers:
        for idx, paper in enumerate(papers, 1):
            with st.container():
                st.markdown(f"**{idx}. {paper.get('title', 'No Title')}**")
              

                if "matched_pairs" in paper:
                    pairs_str = " | ".join(paper["matched_pairs"])
                    st.caption(f"**Matched Pair(s):** {pairs_str}")

                
                col1, col2, col3 = st.columns([2, 2, 3])
                with col1:
                    st.caption(f"Year: {paper.get('year', 'N/A')}")
                with col2:
                    sources = paper.get('sources', [paper.get('source', 'Unknown')])
                    st.caption(f"Sources: {', '.join(sources)}")
                with col3:
                    doi = paper.get('doi')
                    details = paper.get('details', '')
                    content = []
                    if doi:
                        content.append(f"[DOI: {doi}](https://doi.org/{doi})")
                    
                    # Ensure Details/Match Scores are shown
                    if details:
                         content.append(details)
                    
                    st.caption(" | ".join(content))
                
                st.divider()
    else:
        st.info("No collaboration papers found in the databases.")

# --- Main App ---

# Initialize database
# init_db()



with st.container():
    st.header("Conflicts of Interest (COI) Check")
    st.caption("Enter one name per line: First name; Last name")
    
    col1, col2 = st.columns(2)
    with col1:
        # Use session state to preserve input on rerun
        fixed_input = st.text_area(
            "Potential COI", 
            value=st.session_state.fixed_input,
            height=150,
            key="fixed_input_widget"
        )
        st.session_state.fixed_input = fixed_input

    with col2:
        candidate_input = st.text_area(
            "Author(s)", 
            value=st.session_state.candidate_input,
            height=150,
            key="candidate_input_widget"
        )
        st.session_state.candidate_input = candidate_input
    
    # Check unified status
    status, status_message = search_lock.get_status()
    
    if status != "ready":
        st.warning(status_message)

    # Start Search button
    can_search = (status == "ready")
    
    if st.button("Start Search", disabled=not can_search):
        if not fixed_input.strip() or not candidate_input.strip():
            st.error("⚠️ Please enter both Potential COI names and Author(s) to proceed.")
        else:
            # Acquire lock
            if not search_lock.try_acquire():
                st.error(status_message if status_message else "⚠️ System busy, please try again.")
            else:
                try:
                    # Update searching state
                    st.session_state.is_searching = True
                    
                    job_title = "COI Check Results"
                    
                    fixed_authors = [n.strip() for n in fixed_input.split('\n') if n.strip()]
                    candidate_authors = [n.strip() for n in candidate_input.split('\n') if n.strip()]
                    
                    st.info(f"Checking {len(fixed_authors)} potential COI against {len(candidate_authors)} author(s)...")
                    
                    all_raw_results = []
                    generated_search_terms = {}
                    
                    # Pre-generate Combined Search Queries
                    generated_queries = {} 
                    
                    # 1. Prepare all candidate components
                    candidate_wos_parts = []
                    candidate_gs_parts = []
                    
                    for c_name in candidate_authors:
                        c_g, c_f = parse_semicolon_name(c_name)
                        if not c_f: continue
                        
                        # WOS variants for this candidate
                        c_wos_vars = generate_wos_search_term(c_g, c_f)
                        if c_wos_vars:
                            candidate_wos_parts.append("(" + " OR ".join(c_wos_vars) + ")")
                            
                        # GS variants for this candidate
                        c_gs_vars = generate_google_scholar_author_search_term(c_f, c_g)
                        if c_gs_vars:
                            candidate_gs_parts.append("(" + " OR ".join(c_gs_vars) + ")")
                    
                    # Join all candidates with OR
                    all_candidates_wos_str = " OR ".join(candidate_wos_parts)
                    all_candidates_gs_str = " OR ".join(candidate_gs_parts)
                    
                    # 2. For each Fixed Author, create the AND query
                    for f_name in fixed_authors:
                        f_g, f_f = parse_semicolon_name(f_name)
                        if not f_f: continue
                        
                        # WOS
                        f_wos_vars = generate_wos_search_term(f_g, f_f)
                        if f_wos_vars and all_candidates_wos_str:
                            fixed_wos_part = " OR ".join(f_wos_vars)
                            final_wos = f"({fixed_wos_part}) AND ({all_candidates_wos_str})"
                        else:
                            final_wos = "Could not generate query (missing terms)"

                        # GS
                        f_gs_vars = generate_google_scholar_author_search_term(f_f, f_g)
                        if f_gs_vars and all_candidates_gs_str:
                            fixed_gs_part = " OR ".join(f_gs_vars)
                            final_gs = f"({fixed_gs_part}) AND ({all_candidates_gs_str})"
                        else:
                            final_gs = "Could not generate query (missing terms)"
                            
                        display_name = f"{f_f} {f_g}"
                        generated_queries[display_name] = {
                            "wos": final_wos,
                            "gs": final_gs
                        }
                    
                    # Use st.status for a better progress experience
                    with st.status("Checking potential conflicts...", expanded=True) as status:
                        processed = 0
                        total = len(fixed_authors) * len(candidate_authors)
                        
                        for f_name in fixed_authors:
                            f_given, f_family = parse_semicolon_name(f_name)
                            for c_name in candidate_authors:
                                c_given, c_family = parse_semicolon_name(c_name)
                                
                                # Update status label with current pair
                                status.update(label=f"Checking ({processed+1}/{total}): {f_family} vs {c_family}", state="running")
                                st.write(f"Searching: **{f_family}, {f_given}** & **{c_family}, {c_given}**...")
                                
                                res_pm = fetch_pubmed(f_given, f_family, c_given, c_family)
                                res_oa = fetch_openalex(f_given, f_family, c_given, c_family)
                                res_cr = fetch_crossref(f_given, f_family, c_given, c_family)
                                res_s2 = fetch_semanticscholar(f_given, f_family, c_given, c_family)
                                res_doaj = fetch_doaj(f_given, f_family, c_given, c_family)
                                
                                current_pair_name = f"COI: {f_family}, {f_given} with Author: {c_family}, {c_given}"
                                combined_res = res_pm + res_oa + res_cr + res_s2 + res_doaj
                                for r in combined_res:
                                    r["matched_pair"] = current_pair_name
                                
                                all_raw_results.extend(combined_res)
  
                                
                                processed += 1
                        
                        status.update(label="Search Completed!", state="complete", expanded=False)
                    unique_results = merge_results(all_raw_results)
                    
                    # Database save reset
                    input_data = {
                        "fixed": fixed_input,
                        "candidate": candidate_input
                    }
                        
                    # save_results_to_db call removed
                    # st.toast(f"✓ Results saved: '{save_name}'")
                    
                    st.success("Search completed successfully!")

                    # Auto - Popup
                    # wrapping in a clean structure for the dialog
                    complex_result = {
                        "papers": unique_results,
                        "search_terms": generated_queries,
                        "inputs": input_data
                    }
                    
                    # Add to history queue
                    timestamp_str = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    st.session_state.history_queue.append({
                        "timestamp": timestamp_str,
                        "title": job_title,
                        "data": complex_result
                    })
                    
                    show_detail_dialog(job_title, timestamp_str, complex_result)
                
                except Exception as e:
                    st.error(f"An error occurred during search: {e}")
                finally:
                    # Always release lock
                    search_lock.release()
                    st.session_state.is_searching = False

st.divider()

# --- History Queue UI ---
if st.session_state.history_queue:
    st.subheader("Search History (Session)")
    
    # Display in reverse order (newest first)
    # We use enumerate to get unique indices for keys
    for i, item in enumerate(reversed(st.session_state.history_queue)):
        with st.container():
            col1, col2 = st.columns([4, 1])
            with col1:
                st.markdown(f"**{item['timestamp']}**")
                # Showing a brief preview could be nice, e.g. the first fixed author vs first candidate
                preview = "Results View"
                try:
                     f_auth = item['data']['inputs']['fixed'].split('\n')[0][:20]
                     c_auth = item['data']['inputs']['candidate'].split('\n')[0][:20]
                     preview = f"{f_auth}... vs {c_auth}..."
                except:
                    pass
                st.caption(preview)
                
            with col2:
                # Unique key is important here. 
                # Since we are iterating reversed list, 'i' will be 0 for the newest item.
                if st.button("View", key=f"hist_view_{len(st.session_state.history_queue) - 1 - i}"):
                    show_detail_dialog(item['title'], item['timestamp'], item['data'])
            
            st.divider()




