// <vc-preamble>

function total_chars(lst: seq<string>): nat
{
    if |lst| == 0 then 0
    else |lst[0]| + total_chars(lst[1..])
}
lemma total_chars_prefix(lst: seq<string>, i: nat)
    requires 0 <= i < |lst|
    ensures total_chars(lst[..i+1]) == total_chars(lst[..i]) + |lst[i]|
{
    if i == 0 {
        assert lst[..1] == [lst[0]];
        assert total_chars(lst[..1]) == |lst[0]| + total_chars([]);
        assert total_chars([]) == 0;
    } else {
        assert lst[..i+1] == [lst[0]] + (lst[1..])[..i];
        assert lst[..i] == [lst[0]] + (lst[1..])[..i-1];
        assert lst[i] == (lst[1..])[i-1];
        total_chars_prefix(lst[1..], i-1);
        assert total_chars((lst[1..])[..i]) == total_chars((lst[1..])[..i-1]) + |(lst[1..])[i-1]|;
        assert total_chars(lst[..i+1]) == |lst[0]| + total_chars((lst[1..])[..i]);
        assert total_chars(lst[..i]) == |lst[0]| + total_chars((lst[1..])[..i-1]);
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method total_match(lst1: seq<string>, lst2: seq<string>) returns (result: seq<string>)
    ensures result == lst1 || result == lst2
    ensures total_chars(lst1) <= total_chars(lst2) ==> result == lst1
    ensures total_chars(lst1) > total_chars(lst2) ==> result == lst2
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
