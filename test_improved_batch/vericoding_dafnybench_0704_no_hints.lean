/-
  Port of vericoding_dafnybench_0704_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mod (x : Int) (m : Int) : Int :=
  if x < 0 then mod(m + x, m) else if x < m then x else mod(x - m, m)

def div (x : Int) (d : Int) : Int :=
  x/d

def mod (x : Int) (d : Int) : Int :=
  x%d

def div_recursive (x : Int) (d : Int) : Int :=
  function mod_recursive(x:Int, d:Int) : Int requires d > 0; function mod_boogie(x:Int, y:Int) : Int requires y ≠ 0; function div_boogie(x:Int, y:Int) : Int requires y ≠ 0; function my_div_recursive(x:Int, d:Int) : Int requires d ≠ 0; if d > 0 then my_div_pos(x, d) else -1 * my_div_pos(x, -1*d) } function my_div_pos(x:Int, d:Int) : Int requires d >  0; if x < 0 then -1 + my_div_pos(x+d, d) else if x < d then 0 else 1 + my_div_pos(x-d, d) } function my_mod_recursive(x:Int, m:Int) : Int requires m > 0; if x < 0 then my_mod_recursive(m + x, m) else if x < m then x else my_mod_recursive(x - m, m) } //- Kept for legacy reasons: //-static function INTERNAL_mod_boogie(x:Int, m:Int) : Int   { x % y } function INTERNAL_mod_recursive(x:Int, m:Int) : Int requires m > 0; //-static function INTERNAL_div_boogie(x:Int, m:Int) : Int   { x / m } function INTERNAL_div_recursive(x:Int, d:Int) : Int requires d ≠ 0; /* ghost method mod_test() } */ }

end DafnyBenchmarks