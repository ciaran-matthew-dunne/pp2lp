Within the B-Method ecosystem, the Predicate Prover (PP) is an automated theorem
prover that discharges first-order proof obligations. Because PP’s source code 
is not publicly available, its results are currently trusted without independent
verification. We present pp2lp, a tool that reconstructs PP proofs in LambdaPi,
a proof assistant based on the λΠ-calculus modulo rewriting. 
  Each of PP’s inference rules is encoded as a LambdaPi symbol whose type 
captures the rule’s premises and conclusion and whose body proves the rule sound
with respect to classical first-order logic. PP can be instrumented to emit
replays of its proofs; pp2lp parses the replay, rebuilds the proof tree, 
and emits a tactic script that LambdaPi independently type-checks. 
We prove the soundness of nearly all of PP’s inference rules and reconstruct
proofs across several benchmark suites, both real-world and synthetic.
