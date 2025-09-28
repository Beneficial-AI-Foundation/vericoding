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
/* helper modified by LLM (iteration 3): added assertion to prove postcondition */
method ComputeTotalChars(lst: seq<string>) returns (total: nat)
    ensures total == total_chars(lst)
{
    total := 0;
    var i: nat := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant total == total_chars(lst[..i])
    {
        total_chars_prefix(lst, i);
        total := total + |lst[i]|;
        i := i + 1;
    }
    assert lst[..|lst|] == lst;
}
// </vc-helpers>

// <vc-spec>
method total_match(lst1: seq<string>, lst2: seq<string>) returns (result: seq<string>)
    ensures result == lst1 || result == lst2
    ensures total_chars(lst1) <= total_chars(lst2) ==> result == lst1
    ensures total_chars(lst1) > total_chars(lst2) ==> result == lst2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): logic is correct, relies on fixed helper */
    var tc1 := ComputeTotalChars(lst1);
    var tc2 := ComputeTotalChars(lst2);
    if tc1 <= tc2 {
        result := lst1;
    } else {
        result := lst2;
    }
}
// </vc-code>
