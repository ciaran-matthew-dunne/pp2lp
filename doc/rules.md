# Annexe A -- Recapitulatif des regles utilisees

Summary of all inference rules used by the Predicate Prover (PP).

Notation: `H ⊢ P` is a sequent with hypotheses H and conclusion P. Antecedents are premises; the consequent is the conclusion. Rules are applied backwards (from consequent to antecedents). `⇝` denotes "yields result". `◇` = `∃`, `♡` = `forall2`.

## A.1 Conjunction

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AND1 | H ⊢ ¬Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ ¬(P ∧ Q) ⇒ R |
| AND2 | H ⊢ P ⇒ ¬Q | H ⊢ ¬(P ∧ Q) |
| AND3 | H ⊢ P ⇒ (Q ⇒ R) | H ⊢ (P ∧ Q) ⇒ R |
| AND4 | H ⊢ Q; H ⊢ P | H ⊢ P ∧ Q |
| AND5 | P ∧ ··· contains A; H ⊢ P ∧ ··· ∧ B ∧ ··· ⇒ R | H ⊢ P ∧ ··· ∧ (A ⇒ B) ∧ ··· ⇒ R |

## A.2 Disjunctions

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| OR1 | H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ∨ Q) ⇒ R |
| OR2 | H ⊢ ¬Q; H ⊢ ¬P | H ⊢ ¬(P ∨ Q) |
| OR3 | H ⊢ Q ⇒ R; H ⊢ P ⇒ R | H ⊢ (P ∨ Q) ⇒ R |
| OR4 | H ⊢ ¬P ⇒ Q | H ⊢ P ∨ Q |

## A.3 Implications

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| IMP1 | H ⊢ P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ⇒ Q) ⇒ R |
| IMP2 | H ⊢ ¬Q; H ⊢ P | H ⊢ ¬(P ⇒ Q) |
| IMP3 | H ⊢ Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ (P ⇒ Q) ⇒ R |
| IMP4 | H, P ⊢ Q | H ⊢ P ⇒ Q |
| IMP5 | P est dans H; H ⊢ Q | H ⊢ P ⇒ Q |

| Rule | Antecedents | Consequent | Result |
|------|-------------|------------|--------|
| IMP4' | (H, P ⊢ Q) ⇝ R | H ⊢ P ⇒ Q | P ⇒ R |

## A.4 Equivalence

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EQV1 | H ⊢ P ⇒ (¬Q ⇒ R); H ⊢ ¬P ⇒ (Q ⇒ R) | H ⊢ ¬(P ⇔ Q) ⇒ R |
| EQV2 | H ⊢ P ⇒ ¬Q; H ⊢ ¬Q ⇒ P | H ⊢ ¬(P ⇔ Q) |
| EQV3 | H ⊢ P ⇒ (Q ⇒ R); H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ (P ⇔ Q) ⇒ R |
| EQV4 | H ⊢ P ⇒ Q; H ⊢ Q ⇒ P | H ⊢ P ⇔ Q |

## A.5 Negations

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NOT1 | H ⊢ P ⇒ R | H ⊢ ¬¬P ⇒ R |
| NOT2 | H ⊢ P | H ⊢ ¬¬P |

## A.6 Axioms

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AXM1 | ¬P est dans H | H ⊢ P ⇒ Q |
| AXM2 | P est dans H | H ⊢ ¬P ⇒ Q |
| AXM3 | P est dans H | H ⊢ P |
| AXM4 | R est dans H | H ⊢ P ⇒ R |
| AXM5 | ¬Q est dans H | H ⊢ P ⇒ (Q ⇒ R) |
| AXM6 | Q est dans H | H ⊢ P ⇒ (¬Q ⇒ R) |
| AXM7 | *(none)* | H ⊢ P ⇒ P |
| AXM8 | P ∧ ··· contains R | H ⊢ P ∧ ··· ⇒ R |
| AXM9 | ∀x·¬(VRAI ∧ P) est dans H; on a E tel que [x := E] P = R | H ⊢ R ⇒ Q |

## A.7 Universal quantification

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| ALL1 | x et y sont distinctes; H ⊢ ¬(∀(x,y)·P) ⇒ R | H ⊢ ¬(∀x·∀y·P) ⇒ R |
| ALL2 | x et y sont distinctes; H ⊢ ¬(∀(x,y)·P) | H ⊢ ¬(∀x·∀y·P) |
| ALL3 | x et y sont distinctes; H ⊢ (∀(x,y)·P) ⇒ R | H ⊢ (∀x·∀y·P) ⇒ R |
| ALL4 | x et y sont distinctes; H ⊢ ∀(x,y)·P | H ⊢ ∀x·∀y·P |
| ALL5 | x non libre dans R; H ⊢ ∀x·(¬P ⇒ R) | H ⊢ ¬(∀x·P) ⇒ R |
| ALL5 | x est libre dans R; y n'est libre ni dans P ni dans R; S = [x := y] P; H ⊢ ∀y·(¬S ⇒ R) | H ⊢ ¬(∀x·P) ⇒ R |
| ALL6 | H ⊢ (∀x·P) ⇒ FAUX | H ⊢ ¬(∀x·P) |
| ALL7 | x non libre dans H; (H ⊢ P) ⇝ R; H ⊢ (◇x·R) ⇒ Q | H ⊢ (∀x·P) ⇒ Q |
| ALL7 | x est libre dans H; y n'est libre ni dans A ni dans H; P = [x := y] A; (H ⊢ P) ⇝ R; H ⊢ (◇x·R) ⇒ Q | H ⊢ (∀x·A) ⇒ Q |
| ALL8 | x non libre dans H; H ⊢ P | H ⊢ ∀x·P |
| ALL8 | x est libre dans H; y n'est libre ni dans P ni dans H; R = [x := y] P; H ⊢ R | H ⊢ ∀x·P |
| ALL9 | H, (∀x·T) ⊢ Q | H ⊢ (♡x·T) ⇒ Q |

| Rule | Antecedents | Consequent | Result |
|------|-------------|------------|--------|
| ALL7' | x non libre dans H; (H ⊢ P) ⇝ R; (H ⊢ (◇x·R) ⇒ Q) ⇝ S | H ⊢ (∀x·P) ⇒ Q | S |
| ALL7' | x est libre dans H; y n'est libre ni dans A ni dans H; P = [x := y] A; (H ⊢ P) ⇝ R; (H ⊢ (◇x·R) ⇒ Q) ⇝ S | H ⊢ (∀x·A) ⇒ Q | S |
| ALL8' | x non libre dans H; (H ⊢ P) ⇝ Q | H ⊢ ∀x·P | ∀x·Q |
| ALL8' | x est libre dans H; y n'est libre ni dans P ni dans H; R = [x := y] P; (H ⊢ R) ⇝ Q | H ⊢ ∀x·P | ∀y·Q |
| ALL9' | (H, (∀x·P) ⊢ Q) ⇝ R | H ⊢ (♡x·P) ⇒ Q | (∀x·P) ⇒ R |

## A.8 Existential quantification

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| XST1 | x et y sont distinctes; H ⊢ ¬(∃(x,y)·P) ⇒ R | H ⊢ ¬(∃x·∃y·P) ⇒ R |
| XST2 | x et y sont distinctes; H ⊢ ¬(∃(x,y)·P) | H ⊢ ¬(∃x·∃y·P) |
| XST3 | x et y sont distinctes; H ⊢ (∃(x,y)·P) ⇒ R | H ⊢ (∃x·∃y·P) ⇒ R |
| XST4 | x et y sont distinctes; H ⊢ ∃(x,y)·P | H ⊢ ∃x·∃y·P |
| XST5 | H ⊢ (∀x·¬P) ⇒ R | H ⊢ ¬(∃x·P) ⇒ R |
| XST51 | H ⊢ (∀x·P) ⇒ R | H ⊢ ¬(∃x·¬P) ⇒ R |
| XST6 | H ⊢ ∀x·¬P | H ⊢ ¬(∃x·P) |
| XST61 | H ⊢ ∀x·P | H ⊢ ¬(∃x·¬P) |
| XST7 | x non libre dans R; H ⊢ ∀x·(P ⇒ R) | H ⊢ (∃x·P) ⇒ R |
| XST7 | x est libre dans R; y n'est libre ni dans P ni dans R; Q = [x := y] P; H ⊢ ∀y·(Q ⇒ R) | H ⊢ (∃x·P) ⇒ R |
| XST8 | x non libre dans H; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x·R) ⇒ FAUX | H ⊢ ∃x·P |
| XST8 | x est libre dans H; y n'est libre ni dans A ni dans H; P = [x := y] A; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x·R) ⇒ FAUX | H ⊢ (∃x·A) |

## A.9 Vrai et Faux

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| VR1 | *(none)* | H ⊢ ¬VRAI ⇒ R |
| VR2 | H ⊢ FAUX | H ⊢ ¬VRAI |
| VR3 | H ⊢ R | H ⊢ VRAI ⇒ R |
| VR4 | *(none)* | H ⊢ VRAI |
| FX1 | H ⊢ R | H ⊢ ¬FAUX ⇒ R |
| FX2 | *(none)* | H ⊢ ¬FAUX |
| FX3 | *(none)* | H ⊢ FAUX ⇒ R |

## A.10 Regles STOP

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| STOP | P n'est pas le predicat FAUX; H ⊢ ¬P ⇒ FAUX | H ⊢ P |

| Rule | Antecedents | Consequent | Result |
|------|-------------|------------|--------|
| STOP' | *(none)* | H ⊢ P | P |

## A.11 Regle INS

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| INS | Determination des instanciations Q1, Q2, ..., Qn; H ⊢ Q1 ⇒ (Q2 ⇒ ... (Qn ⇒ FAUX)...) | H ⊢ FAUX |

## A.12 Normalisation

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM1 | x non libre dans P; H ⊢ P ⇒ S | H ⊢ (◇x·P) ⇒ S |
| NRM2 | x non libre dans P; H ⊢ (P ⇒ ◇x·Q) ⇒ S | H ⊢ ◇x·(P ⇒ Q) ⇒ S |
| NRM3 | x non libre dans Q; Q n'est pas le predicat FAUX; H ⊢ (Q ⇒ S) ∧ ((∀x·¬P) ⇒ S) | H ⊢ ◇x·(P ⇒ Q) ⇒ S |
| NRM4 | x non libre dans Q; H ⊢ (Q ⇒ ◇x·(P ⇒ R)) ⇒ S | H ⊢ ◇x·(P ⇒ (Q ⇒ R)) ⇒ S |
| NRM5 | H ⊢ ◇x·(P ∧ Q ⇒ R) ⇒ S | H ⊢ ◇x·(P ⇒ (Q ⇒ R)) ⇒ S |
| NRM6 | H ⊢ ◇x·(R ⇒ P) ⇒ (◇x·(R ⇒ Q) ⇒ S) | H ⊢ ◇x·(R ⇒ P ∧ Q) ⇒ S |
| NRM7 | H ⊢ (◇x·P) ⇒ ((◇x·Q) ⇒ S) | H ⊢ ◇x·(P ∧ Q) ⇒ S |
| NRM8 | x et y sont distincts; H ⊢ (◇(x,y)·Q) ⇒ S | H ⊢ (◇x·∀y·Q) ⇒ S |
| NRM8 | x et y ne sont pas distinctes; z est distincte de x et de y; K = [y := z] Q; H ⊢ (◇(x,y)·K) ⇒ S | H ⊢ (◇x·∀y·Q) ⇒ S |
| NRM9 | x et y sont distincts; y non libre dans P; H ⊢ ◇(x,y)·(P ⇒ Q) ⇒ S | H ⊢ ◇x·(P ⇒ ∀y·Q) ⇒ S |
| NRM9 | x et y ne sont pas distinctes ou y est libre dans P; z est distincte de x et non libre dans P et dans Q; K = [y := z] Q; H ⊢ ◇(x,z)·(P ⇒ K) ⇒ S | H ⊢ ◇x·(P ⇒ ∀y·Q) ⇒ S |
| NRM10 | H ⊢ ♡x·¬(P ∧ Q) ⇒ R | H ⊢ ◇x·(P ∧ Q ⇒ FAUX) ⇒ R |
| NRM11 | H ⊢ ♡x·¬(VRAI ∧ P) ⇒ R | H ⊢ ◇x·(P ⇒ FAUX) ⇒ R |
| NRM12 | H ⊢ ♡x·¬(P ∧ Q) ⇒ R | H ⊢ ◇x·(P ⇒ ¬Q) ⇒ R |
| NRM13 | H ⊢ ♡x·¬(P ∧ ¬Q) ⇒ R | H ⊢ ◇x·(P ⇒ Q) ⇒ R |
| NRM14 | H ⊢ ♡x·¬(VRAI ∧ P) ⇒ R | H ⊢ (◇x·¬P) ⇒ R |
| NRM15 | H ⊢ ♡x·¬(VRAI ∧ ¬P) ⇒ R | H ⊢ (◇x·P) ⇒ R |
| NRM16 | ∀x·P est dans H; Q | H ⊢ (♡x·P) ⇒ Q |
| NRM17 | ∀x·¬(VRAI ∧ P) est dans H; on a E tel que [x := E] P = R | H ⊢ ♡y·¬(VRAI ∧ ¬R) ⇒ Q |
| NRM18 | ∀x·¬(VRAI ∧ ¬P) est dans H; on a E tel que [x := E] P = R | H ⊢ ♡y·¬(VRAI ∧ R) ⇒ Q |
| NRM19 | P est dans H; on a E tel que [x := E] R = P | H ⊢ ♡x·¬(VRAI ∧ R) ⇒ Q |
| NRM20 | x non libre dans E; H ⊢ ♡y·¬[x := E] P ⇒ Q | H ⊢ ♡(x,y)·¬(P ∧ x = E) ⇒ Q |
| NRM21 | x non libre dans E; H ⊢ ♡y·¬[x := E] P ⇒ Q | H ⊢ ♡(x,y)·¬(P ∧ E = x) ⇒ Q |
| NRM22 | x non libre dans E; H ⊢ ¬[x := E] P ⇒ Q | H ⊢ ♡x·¬(P ∧ x = E) ⇒ Q |
| NRM23 | x non libre dans E; H ⊢ ¬[x := E] P ⇒ Q | H ⊢ ♡x·¬(P ∧ E = x) ⇒ Q |
| NRM24 | P n'est pas de la forme A ∧ B; H ⊢ ♡x·¬(VRAI ∧ P) ⇒ Q | H ⊢ ♡x·¬P ⇒ Q |
| NRM25 | x non libre dans P; H ⊢ P | H ⊢ forall2(x)·P |
| NRM26 | y non libre dans P; H ⊢ forall2(x,...)·P | H ⊢ forall2(x,y,...)·P |
| NRM27 | (xi ≤ 0) est dans (P ∧ ... ∧ Q); (−xi ≤ 0) est dans (P ∧ ... ∧ Q); on a R tel que [xi := 0](P ∧ ... ∧ Q) = R; H ⊢ ◇(x1,...,xi−1,xi+1,...,xn)·¬R | H ⊢ ♡(x1,...,xn)·¬(P ∧ ... ∧ Q) |
| NRM28 | (x ≤ 0) est dans (P ∧ ... ∧ Q); (−x ≤ 0) est dans (P ∧ ... ∧ Q); on a S tel que [x := 0](P ∧ ... ∧ Q) = S; H ⊢ ¬(S) ⇒ R | H ⊢ (♡(x)·¬(P ∧ ... ∧ Q)) ⇒ R |
| NRM29 | (a + xi ≤ 0) est dans (P ∧ ... ∧ Q); (b − xi ≤ 0) est dans (P ∧ ... ∧ Q); solveur(a + b) = 0; on a S tel que [xi := b](P ∧ ... ∧ Q) = S; H ⊢ ◇(x1,...,xi−1,xi+1,...,xn)·¬S ⇒ R | H ⊢ (♡(x1,...,xn)·¬(P ∧ ... ∧ Q)) ⇒ R |
| NRM29_1 | (xi + a ≤ 0) est dans (P ∧ ... ∧ Q); (−xi + b ≤ 0) est dans (P ∧ ... ∧ Q); solveur(a + b) = 0; on a S tel que [xi := b](P ∧ ... ∧ Q) = S; H ⊢ ◇(x1,...,xi−1,xi+1,...,xn)·¬S ⇒ R | H ⊢ (♡(x1,...,xn)·¬(P ∧ ... ∧ Q)) ⇒ R |
| NRM30 | (a + x ≤ 0) est dans (P ∧ ... ∧ Q); (b − x ≤ 0) est dans (P ∧ ... ∧ Q); solveur(a + b) = 0; on a S tel que [x := b](P ∧ ... ∧ Q) = S; H ⊢ ¬S ⇒ R | H ⊢ (♡x·¬(P ∧ ... ∧ Q)) ⇒ R |
| NRM30_1 | (x + a ≤ 0) est dans (P ∧ ... ∧ Q); (−x + b ≤ 0) est dans (P ∧ ... ∧ Q); solveur(a + b) = 0; on a S tel que [x := b](P ∧ ... ∧ Q) = S; H ⊢ ¬S ⇒ R | H ⊢ (♡x·¬(P ∧ ... ∧ Q)) ⇒ R |

## A.13 Regles sur les egalites

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EVR1 | *(none)* | H ⊢ ¬(E = E) ⇒ P |
| EVR11 | n ∈ N; m ∈ N; n ≠ m | H ⊢ (n = m) ⇒ P |
| EVR2 | H ⊢ FAUX | H ⊢ ¬(E = E) |
| EVR3 | H ⊢ P | H ⊢ (E = E) ⇒ P |
| EVR4 | *(none)* | H ⊢ (E = E) |
| EAXM1 | ¬(F = E) est dans H | H ⊢ (E = F) ⇒ P |
| EAXM2 | (F = E) est dans H | H ⊢ ¬(E = F) ⇒ P |
| EAXM31 | (F = E) est dans H | H ⊢ (E = F) |
| EAXM32 | ¬(F = E) est dans H | H ⊢ ¬(E = F) |
| EIMP51 | ¬(F = E) est dans H; H ⊢ P | H ⊢ ¬(E = F) ⇒ P |
| EIMP52 | (F = E) est dans H; H ⊢ P | H ⊢ (E = F) ⇒ P |
| EQC1 | H ⊢ ¬(a = c) ∨ ¬(b = d) ⇒ P | H ⊢ ¬((a,b) = (c,d)) ⇒ P |
| EQC2 | H ⊢ (a = c) ∧ (b = d) ⇒ P | H ⊢ ((a,b) = (c,d)) ⇒ P |
| EQS1 | H ⊢ E = F ⇒ R | H ⊢ eql_set(E,F) ⇒ R |
| EQS2 | H ⊢ FAUX ⇒ R | H ⊢ ¬eql_set(E,F) ⇒ R |
| EAXM91 | ∀x·¬(VRAI ∧ p = q) est dans H; on a E tel que [x := E](q = p) se reduise a (a = b) | H ⊢ (a = b) ⇒ Q |
| EAXM92 | ∀x·¬(VRAI ∧ ¬(p = q)) est dans H; on a E tel que [x := E](q = p) se reduise a (a = b) | H ⊢ ¬(a = b) ⇒ Q |
| OPR1 | x est une variable; x non libre dans H; x non libre dans E; Q = [x := E] P; H ⊢ Q | H ⊢ (x = E) ⇒ P |
| OPR2 | x est une variable; x non libre dans H; x non libre dans E; Q = [x := E] P; H ⊢ Q | H ⊢ (E = x) ⇒ P |
| ECTR1 | ¬Q est dans H; le remplacement de E par F dans Q donne R; R est dans H | H ⊢ (E = F) ⇒ P |
| ECTR2 | ¬Q est dans H; le remplacement de E par F dans Q donne R; R est dans H | H ⊢ (F = E) ⇒ P |
| ECTR3 | E = F est dans H; le remplacement de E par F dans P donne R; R est dans H | H ⊢ ¬P ⇒ Q |
| ECTR4 | F = E est dans H; le remplacement de E par F dans P donne R; R est dans H | H ⊢ ¬P ⇒ Q |
| ECTR5 | E = F est dans H; le remplacement de E par F dans P donne R; ¬R est dans H | H ⊢ P ⇒ Q |
| ECTR6 | F = E est dans H; le remplacement de E par F dans P donne R; ¬R est dans H | H ⊢ P ⇒ Q |

## A.14 Regles sur l'arithmetique

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AR1 | H ⊢ R | H ⊢ E ≤ E ⇒ R |
| AR2 | a est numerique; b est numerique; a > b | H ⊢ a ≤ b ⇒ R |
| AR3 | H ⊢ 1 − a ≤ 0 ⇒ R | H ⊢ ¬(a ≤ 0) ⇒ R |
| AR4 | F ≤ 0 est dans H; E + F > 0 | H ⊢ E ≤ 0 ⇒ R |
| AR5 | a ≪ 0 est dans H; H ⊢ a = 0 ⇒ (−a ≤ 0 ⇒ R) | H ⊢ −a ≤ 0 ⇒ R |
| AR6 | −a ≪ 0 est dans H; H ⊢ a = 0 ⇒ (a ≤ 0 ⇒ R) | H ⊢ a ≤ 0 ⇒ R |
| AR7 | c + b ≪ 0 est dans H; a + c = 0; H ⊢ a = b ⇒ (a − b ≤ 0 ⇒ R) | H ⊢ a − b ≤ 0 ⇒ R |
| AR8 | a − b ≪ 0 est dans H; a + c = 0; H ⊢ a = b ⇒ (c + b ≤ 0 ⇒ R) | H ⊢ c + b ≤ 0 ⇒ R |
| AR9 | solveur(E) = F; H ⊢ F ≤ 0 ⇒ R | H ⊢ E ≤ 0 ⇒ R |
| AR10 | solveur(P) = Q; H ⊢ Q ⇒ R | H ⊢ P ⇒ R |
| AR11 | *(none)* | H ⊢ not(x ≤ x) ⇒ P |
| AR12 | H, (a ≤ b) ⊢ P | H ⊢ (a ≪ b) ⇒ P |

## A.15 Regles sur les booleens

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| BOOL11 | H, (v = TRUE), ¬(v = FALSE) ⊢ P | H ⊢ (v = TRUE) ⇒ P |
| BOOL12 | H, (v = FALSE), ¬(v = TRUE) ⊢ P | H ⊢ (v = FALSE) ⇒ P |
| BOOL21 | H ⊢ (v = TRUE) ⇒ P | H ⊢ (TRUE = v) ⇒ P |
| BOOL22 | H ⊢ (v = FALSE) ⇒ P | H ⊢ (FALSE = v) ⇒ P |
| BOOL31 | H ⊢ (v = FALSE) ⇒ P | H ⊢ ¬(v = TRUE) ⇒ P |
| BOOL32 | H ⊢ (v = TRUE) ⇒ P | H ⊢ ¬(v = FALSE) ⇒ P |
| BOOL41 | H ⊢ (v = FALSE) ⇒ P | H ⊢ ¬(TRUE = v) ⇒ P |
| BOOL42 | H ⊢ (v = TRUE) ⇒ P | H ⊢ ¬(FALSE = v) ⇒ P |
| BOOL51 | *(none)* | H ⊢ (TRUE = FALSE) ⇒ P |
| BOOL52 | *(none)* | H ⊢ ¬(FALSE = TRUE) ⇒ P |
