use tamarin_parser::{parse_theory, wf};

fn main() {
    let path = std::env::args().nth(1).expect("path");
    let src = std::fs::read_to_string(&path).expect("read");
    let thy = parse_theory(&src, &["diff"]).expect("parse");
    let report = wf::check_theory(&thy);
    for e in &report {
        println!("[{}] {}", e.topic, e.message);
    }
}
