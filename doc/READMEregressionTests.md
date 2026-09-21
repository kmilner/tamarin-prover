# RegressionTests - CI for Tamarin Prover

RegressionTests is a script that runs tests for Tamarin either locally or on [Travis](https://travis-ci.com/github/tamarin-prover/tamarin-prover). 



## Usage

Basic usage is to execute the script without any arguments. To do so, go to the directory root:

```bash
$ cd tamarin-prover
```

and type:

```bash
$ python3 regressionTests.py
```



## What does the script do?

- it calls `stack install` (prevented by `-noi`)
- it runs the case studies (unless `-nom` is given), using `make -j` for parallel execution:
  - `make fast-case-studies sapic-case-studies-fast FAST=y` by default
  - `make case-studies` if `-s` (slow) is given
- for each `.spthy` in the folder `case-studies`
  - it searches for the equivalent in `case-studies-regression` (or another folder specified by `-d`)
  - it parses the steps and times for both files
  - it assures that the files have the same amount of lemmas and they have the same outcome (verified vs. trace-found)
- it outputs the comparison of steps and times depending on the level of verbosity `-v`
- it repeats running the regression tests `-r` times to provide more confidence in time measurements
- it returns `1` if some result/stepcount/file missmatches or other major problems happen

Warning:
- The make command with can take more than an hour to run, consider `-j` if you run on a server with many cores
- The tool does not show any differences in the proofs if the step count didn't change



## Arguments

Here is the output of `python3 regressionTest.py -h`:

```
usage: regressionTests.py [-h] [-s] [-noi] [-nom] [-j JOBS] [-d DIRECTORY]
                          [-r REPEAT] [-v VERBOSE]

optional arguments:
  -h, --help            show this help message and exit
  -s, --slow            Run slow tests (instead of fast tests)
  -noi, --no-install    Do not call 'stack install' before starting the tests
  -nom, --no-make       Do not run regression tests, i.e., do not call 'make case-studies'
  -j JOBS, --jobs JOBS  The amount of Tamarin instances used simultaneously. Each Tamarin instance should have 3 threads and 16GB RAM available
  -d DIRECTORY, --directory DIRECTORY
                        The directory to compare the test results with. The default is case-studies-regression
  -r REPEAT, --repeat REPEAT
                        Repeat everything r times (except for 'stack install'). This gives more confidence in time measurements
  -v VERBOSE, --verbose VERBOSE
                        Level of verbosity, values are from 0 to 5. Default is 2
                        0: show only critical error output and changes of verified vs. trace found
                        1: show summary of time and step differences
                        2: show step differences for changed lemmas
                        3: show time differences for all lemmas
                        4: show shell command output
                        5: show diff output if the corresponding proofs changed
```



## Adding new files to test

To add new files to test, you have to put a reference file in the `case-studies-regression` directory. This reference file **must** **be** an output of a make command.

If you want to add it in fast-tests (and so in Travis), you need to add a Target in the Makefile after `fast-case-studies` and to add the reference file in the `case-studies-regression/fast-tests` subdirectory. The CI offers the for download in the action "Store case-studies as artifacts".



## Travis

To execute this script on Travis, you should think about two things:

- Create all directories and subdirectories in `case-studies` in the `before_install` part of your file `.travis.yml`. Something like this: `  - mkdir -p case-studies case-studies/ake ...`
- Add the following command in the script part: `python3 regressionTests.py -noi`



## Makefile

The Makefile is also important. To make the `fast-case-studies` (used in the script with the fast tests), you should use the command `make fast-case-studies FAST=y`. If you don't precise `FAST=y`, the files will be in the directory `case-studies` and not `case-studies/fast-tests` and the script won't work.





## Contact

For any problem, please contact Philip Lukert.

## Command checks and expected failures

Some regressions concern rejection, translation, or saved-proof handling rather
than the result of a single proof search. Add a companion file named
`<example>.spthy.test.json` beside the affected input to enable these checks.
Examples without a companion file do not get additional prover runs.

`regressionTests.py` discovers companion files under `examples/` and runs their
checks before the ordinary case studies. They also run in CI. No separate shell
script or Makefile target is needed. `--no-make` skips these executions, just as
it skips generating case studies. Each repetition requested with `-r` reruns them.

To run only the command checks, optionally selecting particular companion files:

```sh
python3 regressionTests.py -noi --command-tests-only
python3 regressionTests.py -noi --command-tests-only examples/regression/negative/missing-end.spthy.test.json
python3 regressionTests.py -noi --command-tests-only --tamarin=/path/to/tamarin-prover
```

`--tamarin` selects the executable for command checks, case-study generation,
and existing output-parsing checks. It defaults to the `TAMARIN` environment
variable, or `tamarin-prover` on `PATH`. Use `-noi` with an already built executable;
otherwise the usual `stack install` runs first.

### Negative tests

For example, `examples/regression/negative/missing-end.spthy.test.json` contains:

```json
{
  "tests": [
    {
      "name": "missing-end",
      "args": ["--parse-only"],
      "exit_code": 1,
      "contains": ["unexpected end of input"]
    }
  ]
}
```

Both the exit status and every diagnostic substring must match. A timeout,
signal, missing executable, or unrelated rejection fails the test. Use a stable
part of the diagnostic rather than a full message containing paths or line numbers.
Arguments are passed directly to Tamarin, without a shell. The runner supplies
`-d=0` to disable derivation-check timeouts in these focused tests.

Put intentionally invalid parser inputs in `examples/regression/negative/`.
The Tree-sitter success-only sweep excludes that directory; the command runner
still discovers its companion files.

### Comparing exports and saved proofs

Use an existing regression baseline as the expected result:

```json
{
  "tests": [
    {
      "name": "saved-diff-proofs",
      "args": ["--diff", "--quit-on-warning"],
      "checks": ["roundtrip"]
    }
  ]
}
```

For these checks, the baseline is inferred from the example's path under
`examples/`: `ccs15/probEnc.spthy` uses `ccs15/probEnc_analyzed-diff.spthy`
when `args` includes `--diff`, or `ccs15/probEnc_analyzed.spthy` otherwise.
Only set `baseline` to override this convention for a differently named target.

These paths are relative to `case-studies-regression/fast-tests/`, or to
`case-studies-regression/` with `--slow`. `--directory` changes that root using
the same convention as ordinary regression comparisons. A missing baseline or
missing proof summary fails the test. The runner never updates baselines.

The runner first proves the source. Each requested check then
compares its proof results with that same baseline:

- `roundtrip`: print without proofs and prove the reloaded output; also replay
  the saved original proof without `--prove`.
- `partial-evaluation`: prove the partially evaluated source; export without
  proofs and prove the reloaded output; replay the saved evaluated proof; and
  partially evaluate and prove the unproved export again.

Both checks can be requested together. Comparisons preserve lemma names,
quantifiers, LHS/RHS labels, duplicate results, and verdicts (including incomplete
results), but ignore proof-step counts and timings. In particular, two equally
wrong runs do not pass merely because they agree with each other. The ordinary
baseline comparison still checks step counts as before.

For these proof checks, leave `--prove`, `--partial-evaluation`, and output paths
out of `args`: the runner controls them separately for each step. Tests without
`checks` or a `baseline` override run their specified command once, expecting exit
status zero by default. An explicit `baseline` without `checks` compares just the source proof.

### Other output assertions

`contains` checks literal substrings in the combined stdout/stderr. `matches`
can count regular-expression matches, for example to bound generated rule growth:

```json
"matches": [
  {"regex": "^rule ", "min": 8, "max": 52, "theory_only": true}
]
```

Either bound can be omitted; use equal bounds for an exact count. Regexes use
Python syntax with multiline matching. `theory_only` removes comments (including nested comments) before
counting, so source-process comments cannot masquerade as generated rules.
Assertions apply to every invocation in a test. For checks specific to one export
format, add a separate test with that format in `args`.

`fact_arities` bounds the number of arguments in generated facts, for example
to check that SAPIC intermediate facts do not retain unnecessary variables:

```json
"fact_arities": {"Let_[0-9]+": 2}
```

Each regex matches a whole fact name and maps to its maximum allowed arity.
At least one matching fact must occur, and every occurrence must fit the bound.
Comments are ignored; commas inside nested function applications, tuples, or
quoted strings do not count as argument separators.

Each test needs a unique `name` within its companion file. Optional `timeout`
sets a positive per-invocation limit in seconds (default 120). On POSIX systems a
timeout kills the process group, including Maude. Set `slow` to `true` for tests
that should run only with `--slow`; other tests run in both suites. Unknown fields
and malformed settings fail rather than silently disabling a check.

Logs and generated theories are kept under `case-studies/command-tests/`, grouped
by input and test name, and included in the existing CI artifact. Generated
copies use a `.theory` extension so the ordinary `.spthy` baseline scan does not
pick them up. They are diagnostic artifacts, never expected results.

The runner itself has tests that need no Tamarin build:

```sh
python3 -m unittest discover -s tests -p test_regression_commands.py
```
