predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 10 && 1 <= b <= 10 && 1 <= c <= 10
}

function AllExpressions(a: int, b: int, c: int): seq<int>
{
    [a * b * c, a + b * c, a * b + c, a * (b + c), (a + b) * c, a + b + c]
}

function MaxExpression(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var exprs := AllExpressions(a, b, c);
    if exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5] then exprs[0]
    else if exprs[1] >= exprs[2] && exprs[1] >= exprs[3] && exprs[1] >= exprs[4] && exprs[1] >= exprs[5] then exprs[1]
    else if exprs[2] >= exprs[3] && exprs[2] >= exprs[4] && exprs[2] >= exprs[5] then exprs[2]
    else if exprs[3] >= exprs[4] && exprs[3] >= exprs[5] then exprs[3]
    else if exprs[4] >= exprs[5] then exprs[4]
    else exprs[5]
}

predicate IsMaxOfAllExpressions(result: int, a: int, b: int, c: int)
    requires ValidInput(a, b, c)
{
    var exprs := AllExpressions(a, b, c);
    result in exprs && forall i :: 0 <= i < |exprs| ==> result >= exprs[i]
}

// <vc-helpers>
lemma MaxInSequence(exprs: seq<int>)
    requires |exprs| > 0
    ensures exists i :: 0 <= i < |exprs| && exprs[i] == max(exprs)
{
    if |exprs| == 1 {
        assert exprs[0] == max(exprs);
    } else {
        var subseq := exprs[1..];
        MaxInSequence(subseq);
        var m := max(subseq);
        if exprs[0] > m {
            assert exprs[0] == max(exprs);
        } else {
            assert m == max(exprs);
            var j :| 0 <= j < |subseq| && subseq[j] == m;
            assert exprs[j+1] == m;
        }
    }
}

function max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else
        var m := max(s[1..]);
        if s[0] > m then s[0] else m
}

lemma MaxIsCorrect(s: seq<int>, m: int)
    requires |s| > 0 && m == max(s)
    ensures m in s && forall i :: 0 <= i < |s| ==> m >= s[i]
{
    if |s| == 1 {
        assert s[0] == m;
        assert m in s;
        assert forall i :: 0 <= i < |s| ==> m >= s[i];
    } else {
        var subseq := s[1..];
        var submax := max(subseq);
        MaxIsCorrect(subseq, submax);
        
        if s[0] > submax {
            assert m == s[0];
            assert m in s;
            forall i | 0 <= i < |s| 
                ensures m >= s[i]
            {
                if i == 0 {
                    assert m >= s[i];
                } else {
                    assert m >= submax >= subseq[i-1] == s[i];
                }
            }
        } else {
            assert m == submax;
            assert m in subseq;
            assert m in s;
            forall i | 0 <= i < |s| 
                ensures m >= s[i]
            {
                if i == 0 {
                    assert m >= s[0] by { assert submax >= s[0]; }
                } else {
                    assert m >= subseq[i-1] == s[i];
                }
            }
        }
    }
}

lemma MaxExpressionEqualsMax(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures MaxExpression(a, b, c) == max(AllExpressions(a, b, c))
{
    var exprs := AllExpressions(a, b, c);
    MaxIsCorrect(exprs, max(exprs));
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures IsMaxOfAllExpressions(result, a, b, c)
    ensures result == MaxExpression(a, b, c)
// </vc-spec>
// <vc-code>
{
    var exprs := AllExpressions(a, b, c);
    MaxInSequence(exprs);
    result := max(exprs);
    MaxIsCorrect(exprs, result);
    MaxExpressionEqualsMax(a, b, c);
}
// </vc-code>

