This task implements a function that compares two lists of strings by their total character count. Given two lists of strings, the function should return the list that has the smaller total character count across all its strings. If both lists have the same total character count, return the first list.

// ======= TASK =======
// Given two lists of strings, return the list that has the smaller total character count 
// across all its strings. If both lists have the same total character count, return the first list.

// ======= SPEC REQUIREMENTS =======
function total_chars(lst: seq<string>): nat
{
    if |lst| == 0 then 0
    else |lst[0]| + total_chars(lst[1..])
}

// ======= HELPERS =======
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

// ======= MAIN METHOD =======
method total_match(lst1: seq<string>, lst2: seq<string>) returns (result: seq<string>)
    ensures result == lst1 || result == lst2
    ensures total_chars(lst1) <= total_chars(lst2) ==> result == lst1
    ensures total_chars(lst1) > total_chars(lst2) ==> result == lst2
{
    var total_chars_lst1 := 0;
    var i := 0;
    while i < |lst1|
        invariant 0 <= i <= |lst1|
        invariant total_chars_lst1 == total_chars(lst1[..i])
    {
        total_chars_prefix(lst1, i);
        total_chars_lst1 := total_chars_lst1 + |lst1[i]|;
        i := i + 1;
    }

    var total_chars_lst2 := 0;
    i := 0;
    while i < |lst2|
        invariant 0 <= i <= |lst2|
        invariant total_chars_lst2 == total_chars(lst2[..i])
    {
        total_chars_prefix(lst2, i);
        total_chars_lst2 := total_chars_lst2 + |lst2[i]|;
        i := i + 1;
    }

    assert lst1[..|lst1|] == lst1;
    assert lst2[..|lst2|] == lst2;
    assert total_chars_lst1 == total_chars(lst1);
    assert total_chars_lst2 == total_chars(lst2);

    if total_chars_lst1 <= total_chars_lst2 {
        result := lst1;
    } else {
        result := lst2;
    }
}
