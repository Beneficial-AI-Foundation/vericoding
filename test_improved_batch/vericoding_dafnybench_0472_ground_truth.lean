/-
  Port of vericoding_dafnybench_0472_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function last<T>(s:seq<T>):T
  s[|s|-1]

function all_but_last<T>(s:seq<T>):seq<T>
  s[..|s|-1]

function ConcatenateSeqs<T>(ss:seq<seq<T>>) : seq<T>
  sorry  -- TODO: implement complex function body

function f<T>(s:seq<T>):seq<T>
  sorry  -- TODO: implement function body

function g<T>(ss:seq<seq<T>>) : seq<T>
  sorry  -- TODO: implement function body

end DafnyBenchmarks