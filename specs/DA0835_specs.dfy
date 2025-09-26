// <vc-preamble>
predicate ValidInput(S: string, K: int)
{
    |S| >= 1 && |S| <= 100 &&
    K >= 1 && K <= 1000000000000000000 &&
    forall i :: 0 <= i < |S| ==> S[i] in "123456789"
}

predicate ValidOutput(result: string)
{
    |result| == 1 && result[0] in "123456789"
}

function bitLength(n: int): int
    requires n >= 0
    ensures bitLength(n) >= 1
{
    if n <= 0 then 1
    else if n == 1 then 1
    else 1 + bitLength(n / 2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(S: string, K: int) returns (result: string)
    requires ValidInput(S, K)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    if |S| == 1 {
        result := S;
    } else {
        var s := S;
        var k := K;
        var flg := false;

        while |s| > 0 && s[0] == '1' && k > 1
            invariant forall i :: 0 <= i < |s| ==> s[i] in "123456789"
            invariant k >= 1
        {
            s := s[1..];
            k := k - 1;
        }

        if |s| > 0 && s[0] == '1' && k == 1 {
            result := "1";
            flg := true;
        }

        if !flg {
            if |s| > 0 && s[0] == '2' {
                var bitLen := bitLength(k);
                if bitLen - 1 >= 5000000000000000 {
                    if |s| > 1 {
                        result := [s[1]];
                    } else {
                        result := "2";
                    }
                } else {
                    result := [s[0]];
                }
            } else if |s| > 0 {
                result := [s[0]];
            } else {
                result := "1";
            }
        }
    }
}
// </vc-code>
