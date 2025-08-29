function sum(s: seq<int>) : int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function square_seq(lst: seq<int>) : (sq : seq<int>)
    ensures |sq| == |lst|
{
    seq(|lst|, i requires 0 <= i < |lst| => if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
}

// <vc-helpers>
lemma sum_empty()
    ensures sum([]) == 0
{
}

lemma sum_single(x: int)
    ensures sum([x]) == x
{
}

lemma sum_concat(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 == [s1[0]] + s1[1..];
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        sum_concat(s1[1..], s2);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def sum_squares(lst: List[int]) -> int
This function will take a list of integers. For all entries in the list, the function shall square the integer entry if its index is a multiple of 3 and will cube the integer entry if its index is a multiple of 4 and not a multiple of 3. The function will not change the entries in the list whose indexes are not a multiple of 3 or 4. The function shall then return the sum of all entries.
*/
// </vc-description>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    r := 0;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant r == sum(square_seq(lst[..i]))
    {
        var val := if i % 3 == 0 then lst[i] * lst[i] 
                  else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] 
                       else lst[i]);
        r := r + val;
        i := i + 1;
        
        assert square_seq(lst[..i]) == square_seq(lst[..i-1]) + [val];
        sum_concat(square_seq(lst[..i-1]), [val]);
        assert sum(square_seq(lst[..i])) == sum(square_seq(lst[..i-1])) + val;
    }
    assert lst[..|lst|] == lst;
}
// </vc-code>

