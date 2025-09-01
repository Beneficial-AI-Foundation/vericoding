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
lemma sum_append(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        sum_append(s1[1..], s2);
    }
}

lemma square_seq_slice(lst: seq<int>, i: int)
    requires 0 <= i <= |lst|
    ensures square_seq(lst[..i]) == square_seq(lst)[..i]
{
    if i == 0 {
        assert lst[..0] == [];
        assert square_seq(lst)[..0] == [];
    } else {
        square_seq_slice(lst, i-1);
    }
}

lemma square_seq_tail(lst: seq<int>)
    requires |lst| > 0
    ensures square_seq(lst[1..]) == square_seq(lst)[1..]
{
    var n := |lst|;
    assert |lst[1..]| == n - 1;
    assert |square_seq(lst)[1..]| == n - 1;
    
    forall i | 0 <= i < n - 1
        ensures square_seq(lst[1..])[i] == square_seq(lst)[1..][i]
    {
        var j := i + 1;
        assert lst[1..][i] == lst[j];
        assert square_seq(lst)[1..][i] == square_seq(lst)[j];
        
        assert square_seq(lst[1..])[i] == (if i % 3 == 0 then lst[j] * lst[j] else (if i % 4 == 0 then lst[j] * lst[j] * lst[j] else lst[j]));
        assert square_seq(lst)[j] == (if j % 3 == 0 then lst[j] * lst[j] else (if j % 4 == 0 then lst[j] * lst[j] * lst[j] else lst[j]));
        
        assert (i % 3 == 0) == (j % 3 == 0) by {
            assert j == i + 1;
            if i % 3 == 0 {
                assert (i + 1) % 3 == 1;
                assert j % 3 == 1;
            } else if i % 3 == 1 {
                assert (i + 1) % 3 == 2;
                assert j % 3 == 2;
            } else {
                assert i % 3 == 2;
                assert (i + 1) % 3 == 0;
                assert j % 3 == 0;
            }
        }
        
        assert (i % 4 == 0) == (j % 4 == 0) by {
            assert j == i + 1;
            if i % 4 == 0 {
                assert (i + 1) % 4 == 1;
                assert j % 4 == 1;
            } else if i % 4 == 1 {
                assert (i + 1) % 4 == 2;
                assert j % 4 == 2;
            } else if i % 4 == 2 {
                assert (i + 1) % 4 == 3;
                assert j % 4 == 3;
            } else {
                assert i % 4 == 3;
                assert (i + 1) % 4 == 0;
                assert j % 4 == 0;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if |lst| == 0 {
        r := 0;
        return;
    }
    
    var squared_element := if 0 % 3 == 0 then lst[0] * lst[0] else (if 0 % 4 == 0 then lst[0] * lst[0] * lst[0] else lst[0]);
    var rest_sum := sum_squares(lst[1..]);
    
    square_seq_tail(lst);
    assert square_seq(lst[1..]) == square_seq(lst)[1..];
    sum_append([squared_element], square_seq(lst)[1..]);
    
    r := squared_element + rest_sum;
}
// </vc-code>

