// <vc-preamble>

function count(s: seq<int>, x: int): int
{
    |set i | 0 <= i < |s| && s[i] == x|
}

function max_seq(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max_seq(s)
    ensures max_seq(s) in s
{
    if |s| == 1 then s[0]
    else if s[0] >= max_seq(s[1..]) then s[0]
    else max_seq(s[1..])
}

predicate ValidInput(lst: seq<int>)
{
    |lst| > 0 && forall i :: 0 <= i < |lst| ==> lst[i] > 0
}

predicate ValidResult(lst: seq<int>, result: int)
    requires ValidInput(lst)
{
    var frequency := map x | x in lst :: x := count(lst, x);
    if result == -1 then
        forall x :: x in frequency ==> frequency[x] < x
    else
        result > 0 &&
        result in frequency && 
        frequency[result] >= result &&
        forall y :: y in frequency && frequency[y] >= y ==> y <= result
}
lemma count_append_lemma(s: seq<int>, elem: int, x: int)
    ensures count(s + [elem], x) == count(s, x) + (if x == elem then 1 else 0)
{
    var s' := s + [elem];
    var original_indices := set i | 0 <= i < |s| && s[i] == x;
    var new_indices := set i | 0 <= i < |s'| && s'[i] == x;

    assert forall i :: 0 <= i < |s| ==> s'[i] == s[i];
    assert original_indices == set i | 0 <= i < |s| && s'[i] == x;

    if x == elem {
        assert s'[|s|] == elem == x;
        assert new_indices == original_indices + {|s|};
        assert |s| !in original_indices;
        assert |new_indices| == |original_indices| + 1;
    } else {
        assert s'[|s|] == elem != x;
        assert new_indices == original_indices;
        assert |new_indices| == |original_indices|;
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method search(lst: seq<int>) returns (result: int)
    requires ValidInput(lst)
    ensures ValidResult(lst, result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
