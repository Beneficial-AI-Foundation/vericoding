

// <vc-helpers>
lemma lemma_subset<A(==)>(s: set<A>, t: set<A>)
    ensures s == t <==> s <= t && t <= s
{
}

lemma lemma_set_subset(xs: seq<char>, ys: seq<char>)
    requires forall i :: 0 <= i < |xs| ==> xs[i] in ys
    ensures (set i | i in xs) <= (set i | i in ys)
{
}

lemma lemma_set_equal(xs: seq<char>, ys: seq<char>)
    requires (set i | i in xs) <= (set i | i in ys)
    requires (set i | i in ys) <= (set i | i in xs)
    ensures (set i | i in xs) == (set i | i in ys)
{
    lemma_subset((set i | i in xs), (set i | i in ys));
}

lemma lemma_char_in_string(s: string, c: char)
    ensures c in s == (exists i: int :: 0 <= i < |s| && s[i] == c)
{
}
// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)
    // post-conditions-start
    ensures b == ((set i | i in s0) == (set i | i in s1))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s0| == 0 && |s1| == 0 {
    return true;
  }

  var seen_s0 : set<char> := {};
  var seen_s1 : set<char> := {};
  
  var i := 0;
  while i < |s0|
    invariant 0 <= i <= |s0|
    invariant seen_s0 == (set j | 0 <= j < i :: s0[j])
  {
    if s0[i] !in seen_s0 {
      seen_s0 := seen_s0 + {s0[i]};
    }
    i := i + 1;
  }
  
  i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant seen_s1 == (set j | 0 <= j < i :: s1[j])
  {
    if s1[i] !in seen_s1 {
      seen_s1 := seen_s1 + {s1[i]};
    }
    i := i + 1;
  }
  
  return seen_s0 == seen_s1;
}
// </vc-code>

