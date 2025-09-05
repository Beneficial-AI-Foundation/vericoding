This verification task involves finding the greatest integer in a list whose frequency is greater than or equal to its own value. Given a non-empty list of positive integers, the implementation should return this greatest qualifying integer, or -1 if no such integer exists.

The task requires building a frequency map for all elements in the list, then identifying which elements have frequencies meeting the criteria, and finally selecting the maximum among those valid elements.

// ======= TASK =======
// Given a non-empty list of positive integers, find the greatest integer whose frequency 
// in the list is greater than or equal to its own value. If no such integer exists, return -1.

// ======= SPEC REQUIREMENTS =======
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

// ======= HELPERS =======
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

// ======= MAIN METHOD =======
method search(lst: seq<int>) returns (result: int)
    requires ValidInput(lst)
    ensures ValidResult(lst, result)
{
    var frequency: map<int, int> := map[];
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall x :: x in frequency <==> x in lst[..i]
        invariant forall x :: x in frequency ==> frequency[x] == count(lst[..i], x)
        invariant forall x :: x in frequency ==> frequency[x] > 0
    {
        var num := lst[i];

        assert lst[..i+1] == lst[..i] + [num];
        count_append_lemma(lst[..i], num, num);
        assert count(lst[..i+1], num) == count(lst[..i], num) + 1;
        forall x | x != num 
            ensures count(lst[..i+1], x) == count(lst[..i], x)
        {
            count_append_lemma(lst[..i], num, x);
        }

        if num in frequency {
            frequency := frequency[num := frequency[num] + 1];
        } else {
            frequency := frequency[num := 1];
            assert count(lst[..i], num) == 0;
        }
        i := i + 1;
    }

    assert lst[..|lst|] == lst;
    assert forall x :: x in frequency <==> x in lst;
    assert forall x :: x in frequency ==> frequency[x] == count(lst, x);

    var validNumbers: seq<int> := [];
    var keys := frequency.Keys;

    while keys != {}
        invariant forall x :: x in validNumbers ==> x in frequency && frequency[x] >= x
        invariant forall x :: x in frequency && frequency[x] >= x && x !in keys ==> x in validNumbers
        invariant forall x :: x in validNumbers ==> x > 0
        invariant keys <= frequency.Keys
        decreases |keys|
    {
        var num :| num in keys;
        keys := keys - {num};
        assert num in frequency;

        if frequency[num] >= num {
            validNumbers := validNumbers + [num];
        }
    }

    assert forall x :: x in validNumbers <==> (x in frequency && frequency[x] >= x);

    if |validNumbers| > 0 {
        result := max_seq(validNumbers);
        assert result in validNumbers;
        assert result in frequency && frequency[result] >= result;
        assert forall y :: y in frequency && frequency[y] >= y ==> y <= result;
    } else {
        result := -1;
        assert forall x :: x in frequency ==> frequency[x] < x;
    }
}
