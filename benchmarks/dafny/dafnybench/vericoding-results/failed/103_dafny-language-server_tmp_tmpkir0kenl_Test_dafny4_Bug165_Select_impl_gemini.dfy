// <vc-preamble>
type T
function f(a: T) : bool
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof hints to FilterCorrectness lemma */
function Filter(s: seq<T>): seq<T>
  decreases s
{
  if s == [] then []
  else if f(s[0]) then [s[0]] + Filter(s[1..])
  else Filter(s[1..])
}

lemma FilterCorrectness(s: seq<T>)
  ensures forall e: T :: f(e) ==> multiset(s)[e] == multiset(Filter(s))[e]
  ensures forall e: T :: !f(e) ==> multiset(Filter(s))[e] == 0
  decreases s
{
  if s != [] {
    FilterCorrectness(s[1..]);
    if !f(s[0]) {
      forall e: T | f(e) {
        assert e != s[0];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Select(s1: seq<T>) returns (r: seq<T>)
  ensures (forall e: T  :: f(e) ==> multiset(s1)[e] == multiset(r)[e])
  ensures (forall e: T  :: (!f(e)) ==> 0 == multiset(r)[e])

method Main(s1: seq<T>)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): call correctness lemma before assigning r */
  FilterCorrectness(s1);
  r := Filter(s1);
}
// </vc-code>
