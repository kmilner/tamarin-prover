use tamarin_parser::parse_theory;
use tamarin_theory::elaborate::elaborate;
use tamarin_term::maude_proc::MaudeHandle;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 { eprintln!("usage: dump_variants <theory> <rule_name>"); std::process::exit(2); }
    let theory_path = &args[1];
    let rule_name = &args[2];
    let source = std::fs::read_to_string(theory_path).expect("read");
    let parsed = parse_theory(&source, &[]).expect("parse");
    let elaborated = elaborate(&parsed).expect("elaborate");
    // Resolve maude from $MAUDE_PATH, else `maude` on PATH.
    let maude_path = std::env::var("MAUDE_PATH").unwrap_or_else(|_| "maude".to_string());
    let maude = MaudeHandle::start(&maude_path, elaborated.signature.maude_sig.clone()).expect("maude");
    for open in elaborated.rules() {
        let r = &open.rule;
        let n = match &r.info.name {
            tamarin_theory::rule::ProtoRuleName::Stand(s) => *s,
            _ => "",
        };
        if n == *rule_name {
            println!("rule {}: pre", n);
            for f in &r.premises { println!("  prem: {:?}", f); }
            for f in &r.conclusions { println!("  conc: {:?}", f); }
            for f in &r.actions { println!("  act:  {:?}", f); }
            // Compute variants
            let substs = tamarin_theory::tools::rule_variants::variant_substs_for_rule(&maude, r).expect("variants");
            println!("variants ({}):", substs.len());
            for (i, s) in substs.iter().enumerate() {
                println!("  [{}] {:?}", i, s);
            }
            return;
        }
    }
    eprintln!("rule not found: {}", rule_name);
}
