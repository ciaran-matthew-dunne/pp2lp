require open pp2lp.Rules;
symbol Thm (P : Prd) ≔ □ ⊩ P;

symbol {|30.trace|} :
  Thm ((¬ FALSE)) ≔
begin
  simplify;
  apply FX2
end;
