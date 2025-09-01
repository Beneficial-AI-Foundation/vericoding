

// <vc-helpers>
lemma lemma_subset<A(==)>(s: set<A>, t: set<A>)
    ensures s == t <==> s <= t && t <= s
{
}

lemma lemma_set_subset(xs: seq<char>, ys: seq<char>)
    requires forall i :: 0 <= i < |xs| ==> xs[i] in ys
    ensures set xs <= set ys
{
}

lemma lemma_set_equal(xs: seq<char>, ys: seq<char>)
    requires set xs <= set ys
    requires set ys <= set xs
    ensures set xs == set ys
{
    lemma_subset(set xs, set ys);
}

lemma lemma_char_in_string(s: string, c: char)
    ensures c in s <==> (exists i: int :: 0 <= i < |s| && s[i] == c)
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method same_chars(s0 : string, s1 : string) returns (b : bool)
    // post-conditions-start
    ensures b == ((set i | i in s0) == (set i | i in s1))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var set_s0: set<char> := set s0;
  var set_s1: set<char> := set s1;
  b := set_s0 == set_s1;
}
// </vc-code>

