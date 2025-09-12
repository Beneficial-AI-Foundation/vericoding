/-
  Port of vericoding_dafnybench_0465_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function {:opaque} Hidden(x:int) : (int, int)
  (5, 7)

function Visible(x:int) : (int, int)
  Hidden(x)

function Hidden(x:int) : (int, int)
  (5, 7)

function Visible(x:int) : (int, int)
  Hidden(x)

function {:fuel 0,0} Hidden(x:int) : (int, int)
  (5, 7)

function Visible(x:int) : (int, int)
  Hidden(x)

end DafnyBenchmarks