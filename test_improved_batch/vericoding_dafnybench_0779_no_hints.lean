/-
  Port of vericoding_dafnybench_0779_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function DropLast<T>(theSeq: seq<T>) : seq<T>
  theSeq[..|theSeq|-1]

function Last<T>(theSeq: seq<T>) : T
  theSeq[|theSeq|-1]

function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
  sorry  -- TODO: implement complex function body

function {:opaque} MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
  var m':= map j | j in m ∧ j ≠ key :: m[j]!; m'

def TurnRight (direction : Direction) : Direction :=
  // This function introduces two new bis of syntax. // First, the if-else expression: if <Bool> then T else T // Second, the element.Ctor? built-in predicate, which tests whether // the datatype `element` was built by `Ctor`. if direction.North? then East else if direction.East? then South else if direction.South? then West else  // By elimination, West! North

def TurnLeft (direction : Direction) : Direction :=
  // Another nice way to take apart a datatype element is with match-case // construct. Each case argument is a constructor; each body must be of the // same type, which is the type of the entire `match` expression. match direction { case North => West case West => South case South => East  // Try changing "East" to 7. case East => North }

end DafnyBenchmarks