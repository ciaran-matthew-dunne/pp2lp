require open pp2lp.Proof;

injective symbol π : El prd → TYPE;
//rule π ($p => $q) ↪ π ($p) → π ($q);

symbol AND1 [P Q R] :
  π (not Q => R) →
  π (not P => R) →
  π (not (P and Q) => R);

symbol IMP4 [P Q] :
  (π P → π Q) → π (P => Q);

symbol OR4 [P Q] :
  π ((not P) => Q) →
  π (P or Q);

symbol AXM1 [P Q] :
  π (not P) → π (P => Q);


symbol AXM4 [P R] :
  π (R) → π (P => R);

symbol NOT1 [P R] :
  π (P => R) → π (not not P => R);
