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
function nth_square(lst: seq<int>, i: int) : int
    requires 0 <= i < |lst|
{
    if i % 3 == 0 then lst[i] * lst[i]
    else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i])
}

lemma SumSquareSeq(lst: seq<int>)
    ensures sum(square_seq(lst)) == sum_nth_square(lst, 0)
{
    if |lst| == 0 {
        assert sum(square_seq(lst)) == 0;
        assert sum_nth_square(lst, 0) == 0;
    } else {
        calc {
            sum(square_seq(lst));
            square_seq(lst)[0] + sum(square_seq(lst)[1..]);
            nth_square(lst, 0) + sum(square_seq(lst[1..]));
            {
                assert square_seq(lst)[0] == nth_square(lst, 0) by {
                    if 0 % 3 == 0 {
                        assert square_seq(lst)[0] == lst[0] * lst[0];
                        assert nth_square(lst, 0) == lst[0] * lst[0];
                    } else if 0 % 4 == 0 {
                        assert square_seq(lst)[0] == lst[0] * lst[0] * lst[0];
                        assert nth_square(lst, 0) == lst[0] * lst[0] * lst[0];
                    } else {
                        assert square_seq(lst)[0] == lst[0];
                        assert nth_square(lst, 0) == lst[0];
                    }
                }
            }
            nth_square(lst, 0) + sum_nth_square(lst[1..], 0);
            nth_square(lst, 0) + sum_nth_square(lst, 1);
        }
    }
}

function sum_nth_square(lst: seq<int>, k: int) : int
    requires 0 <= k <= |lst|
    decreases |lst| - k
{
    if k == |lst| then 0
    else nth_square(lst, k) + sum_nth_square(lst, k + 1)
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
    var r_local := 0;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant r_local == sum_nth_square(lst, 0) - sum_nth_square(lst, i)
    {
        r_local := r_local + nth_square(lst, i);
        i := i + 1;
    }
    r := r_local;

    SumSquareSeq(lst);
    assert r == sum_nth_square(lst, 0) by {
        calc {
            r;
            r_local;
            sum_nth_square(lst, 0) - sum_nth_square(lst, i);
            sum_nth_square(lst, 0) - sum_nth_square(lst, |lst|);
            sum_nth_square(lst, 0) - 0;
            sum_nth_square(lst, 0);
        }
    }
}
// </vc-code>

