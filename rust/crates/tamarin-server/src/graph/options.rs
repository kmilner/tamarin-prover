//! Port of `GraphOptions` from `Graph.hs:55-73`.

use std::collections::HashMap;

use super::simplify::SimplificationLevel;

/// Options for graph generation.  Mirror of `GraphOptions`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GraphOptions {
    pub simplification_level: SimplificationLevel,
    pub show_auto_source: bool,
    /// If `true`, cluster by similar rule names; if `false`, cluster
    /// by role.  Matches Haskell `goClustering`.
    pub clustering_similar_names: bool,
    pub abbreviate: bool,
    pub compress: bool,
}

impl Default for GraphOptions {
    fn default() -> Self {
        // Mirror of `defaultGraphOptions` (Graph.hs:66-73).
        GraphOptions {
            simplification_level: SimplificationLevel::SL2,
            show_auto_source: false,
            clustering_similar_names: false,
            abbreviate: true,
            compress: true,
        }
    }
}

/// Build `GraphOptions` from a query-string `?simp=N&compress=0|1&...`.
///
/// Accepted parameters:
/// - `simp` / `simplification`: 0..3
/// - `compress`: 0|1 / true|false
/// - `cluster_names`: 0|1   (when true, use similar-name clustering)
/// - `abbrev`: 0|1
/// - `auto_sources`: 0|1
pub fn graph_options_from_query(qs: &str) -> GraphOptions {
    let mut opts = GraphOptions::default();
    let params: HashMap<String, String> = qs.split('&')
        .filter_map(|kv| {
            let mut it = kv.splitn(2, '=');
            let k = it.next()?;
            let v = it.next().unwrap_or("");
            Some((k.to_string(), v.to_string()))
        }).collect();
    if let Some(v) = params.get("simp").or_else(|| params.get("simplification")) {
        if let Ok(n) = v.parse::<u8>() {
            opts.simplification_level = SimplificationLevel::from_u8(n);
        }
    }
    if let Some(v) = params.get("compress") {
        opts.compress = parse_bool(v).unwrap_or(opts.compress);
    }
    if let Some(v) = params.get("cluster_names") {
        opts.clustering_similar_names = parse_bool(v).unwrap_or(false);
    }
    if let Some(v) = params.get("abbrev") {
        opts.abbreviate = parse_bool(v).unwrap_or(opts.abbreviate);
    }
    if let Some(v) = params.get("auto_sources") {
        opts.show_auto_source = parse_bool(v).unwrap_or(opts.show_auto_source);
    }
    opts
}

fn parse_bool(s: &str) -> Option<bool> {
    match s.to_ascii_lowercase().as_str() {
        "1" | "true" | "yes" | "on" => Some(true),
        "0" | "false" | "no" | "off" | "" => Some(false),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_match_haskell() {
        let o = GraphOptions::default();
        assert_eq!(o.simplification_level, SimplificationLevel::SL2);
        assert!(!o.show_auto_source);
        assert!(!o.clustering_similar_names);
        assert!(o.abbreviate);
        assert!(o.compress);
    }

    #[test]
    fn parse_query_simp_and_compress() {
        let o = graph_options_from_query("simp=3&compress=0");
        assert_eq!(o.simplification_level, SimplificationLevel::SL3);
        assert!(!o.compress);
    }

    #[test]
    fn parse_query_cluster_names() {
        let o = graph_options_from_query("cluster_names=1");
        assert!(o.clustering_similar_names);
    }

    #[test]
    fn parse_query_unknown_param_keeps_defaults() {
        let o = graph_options_from_query("unknown=42");
        assert_eq!(o, GraphOptions::default());
    }

    #[test]
    fn parse_query_simp_invalid_falls_back() {
        let o = graph_options_from_query("simp=bogus");
        assert_eq!(o.simplification_level, SimplificationLevel::SL2);
    }
}
