// <vc-preamble>
predicate ValidInput(n: int, m: int, strings: seq<string>)
{
    n >= 3 && m >= 1 && |strings| == n &&
    (forall i :: 0 <= i < |strings| ==> |strings[i]| == m) &&
    (forall i :: 0 <= i < |strings| ==> forall j :: 0 <= j < |strings[i]| ==> 
        ('0' <= strings[i][j] <= '9') || ('a' <= strings[i][j] <= 'z') || 
        (strings[i][j] == '#') || (strings[i][j] == '*') || (strings[i][j] == '&'))
}

function computeDistanceForString(s: string, needDigit: bool, needSpecial: bool, needLower: bool): int
    requires |s| > 0
    ensures computeDistanceForString(s, needDigit, needSpecial, needLower) >= 0
    ensures computeDistanceForString(s, needDigit, needSpecial, needLower) <= 1000000
{
    if |s| == 0 then 1000000
    else computeDistanceHelper(s, needDigit, needSpecial, needLower, 0, 1000000)
}

function computeDistanceHelper(s: string, needDigit: bool, needSpecial: bool, needLower: bool, i: int, minDist: int): int
    requires |s| > 0
    requires 0 <= i <= |s|
    requires minDist >= 0
    requires minDist <= 1000000
    ensures computeDistanceHelper(s, needDigit, needSpecial, needLower, i, minDist) >= 0
    ensures computeDistanceHelper(s, needDigit, needSpecial, needLower, i, minDist) <= 1000000
    decreases |s| - i
{
    if i >= |s| then minDist
    else
        var ch := s[i];
        var matches := (needDigit && '0' <= ch <= '9') || 
                      (needSpecial && (ch == '#' || ch == '*' || ch == '&')) ||
                      (needLower && 'a' <= ch <= 'z');
        var newMinDist := if matches then min(minDist, min(i, |s| - 1 - i)) else minDist;
        computeDistanceHelper(s, needDigit, needSpecial, needLower, i + 1, newMinDist)
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int {
    if a <= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, strings: seq<string>) returns (result: int)
    requires ValidInput(n, m, strings)
    ensures result >= 0
    ensures result <= 3000000
    ensures (exists i, j, k :: 0 <= i < n && 0 <= j < n && 0 <= k < n && i != j && j != k && i != k &&
        result == computeDistanceForString(strings[i], true, false, false) + 
                 computeDistanceForString(strings[j], false, true, false) + 
                 computeDistanceForString(strings[k], false, false, true))
    ensures (forall i, j, k :: 0 <= i < n && 0 <= j < n && 0 <= k < n && i != j && j != k && i != k ==>
        result <= computeDistanceForString(strings[i], true, false, false) + 
                 computeDistanceForString(strings[j], false, true, false) + 
                 computeDistanceForString(strings[k], false, false, true))
// </vc-spec>
// <vc-code>
{
    var dp: seq<seq<int>> := [];

    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |dp| == i
        invariant forall x :: 0 <= x < i ==> |dp[x]| == 3
        invariant forall x :: 0 <= x < i ==> dp[x][0] >= 0 && dp[x][1] >= 0 && dp[x][2] >= 0
        invariant forall x :: 0 <= x < i ==> dp[x][0] <= 1000000 && dp[x][1] <= 1000000 && dp[x][2] <= 1000000
        invariant forall x :: 0 <= x < i ==> 
            dp[x][0] == computeDistanceForString(strings[x], true, false, false) &&
            dp[x][1] == computeDistanceForString(strings[x], false, true, false) &&
            dp[x][2] == computeDistanceForString(strings[x], false, false, true)
    {
        var s := strings[i];
        var c := 1000000; // distance to digit
        var t := 1000000; // distance to special char
        var l := 1000000; // distance to lowercase

        var j := 0;
        while j < |s|
            invariant 0 <= j <= |s|
            invariant c >= 0 && t >= 0 && l >= 0
            invariant c <= 1000000 && t <= 1000000 && l <= 1000000
        {
            var ch := s[j];
            if '0' <= ch <= '9' {
                c := min(c, min(j, |s| - 1 - j));
            }
            if ch == '#' || ch == '*' || ch == '&' {
                t := min(t, min(j, |s| - 1 - j));
            }
            if 'a' <= ch <= 'z' {
                l := min(l, min(j, |s| - 1 - j));
            }
            j := j + 1;
        }
        dp := dp + [[c, t, l]];
        i := i + 1;
    }

    var bestI, bestJ, bestK := 0, 1, 2;
    var mm := dp[bestI][0] + dp[bestJ][1] + dp[bestK][2];

    // Try all permutations of n taken 3
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant mm >= 0
        invariant mm <= 3000000
        invariant 0 <= bestI < n && 0 <= bestJ < n && 0 <= bestK < n
        invariant bestI != bestJ && bestJ != bestK && bestI != bestK
        invariant mm == dp[bestI][0] + dp[bestJ][1] + dp[bestK][2]
        invariant forall x, y, z :: 0 <= x < i && 0 <= y < n && 0 <= z < n && x != y && y != z && x != z ==>
            mm <= dp[x][0] + dp[y][1] + dp[z][2]
        invariant forall x, y, z :: 0 <= x < n && 0 <= y < n && 0 <= z < n && x != y && y != z && x != z ==>
            dp[x][0] + dp[y][1] + dp[z][2] >= 0
        invariant forall x :: 0 <= x < n ==> 
            dp[x][0] == computeDistanceForString(strings[x], true, false, false) &&
            dp[x][1] == computeDistanceForString(strings[x], false, true, false) &&
            dp[x][2] == computeDistanceForString(strings[x], false, false, true)
    {
        var j := 0;
        while j < n
            invariant 0 <= j <= n
            invariant mm >= 0
            invariant mm <= 3000000
            invariant 0 <= bestI < n && 0 <= bestJ < n && 0 <= bestK < n
            invariant bestI != bestJ && bestJ != bestK && bestI != bestK
            invariant mm == dp[bestI][0] + dp[bestJ][1] + dp[bestK][2]
            invariant (forall x, y, z :: (0 <= x < i && 0 <= y < n && 0 <= z < n && x != y && y != z && x != z) ||
                (x == i && 0 <= y < j && 0 <= z < n && x != y && y != z && x != z) ==>
                mm <= dp[x][0] + dp[y][1] + dp[z][2])
            invariant forall x :: 0 <= x < n ==> 
                dp[x][0] == computeDistanceForString(strings[x], true, false, false) &&
                dp[x][1] == computeDistanceForString(strings[x], false, true, false) &&
                dp[x][2] == computeDistanceForString(strings[x], false, false, true)
        {
            var k := 0;
            while k < n
                invariant 0 <= k <= n
                invariant mm >= 0
                invariant mm <= 3000000
                invariant 0 <= bestI < n && 0 <= bestJ < n && 0 <= bestK < n
                invariant bestI != bestJ && bestJ != bestK && bestI != bestK
                invariant mm == dp[bestI][0] + dp[bestJ][1] + dp[bestK][2]
                invariant (forall x, y, z :: ((0 <= x < i && 0 <= y < n && 0 <= z < n && x != y && y != z && x != z) ||
                    (x == i && 0 <= y < j && 0 <= z < n && x != y && y != z && x != z) ||
                    (x == i && y == j && 0 <= z < k && x != y && y != z && x != z)) ==>
                    mm <= dp[x][0] + dp[y][1] + dp[z][2])
                invariant forall x :: 0 <= x < n ==> 
                    dp[x][0] == computeDistanceForString(strings[x], true, false, false) &&
                    dp[x][1] == computeDistanceForString(strings[x], false, true, false) &&
                    dp[x][2] == computeDistanceForString(strings[x], false, false, true)
            {
                if i != j && j != k && i != k {
                    var tmpCall1 := dp[i][0] + dp[j][1] + dp[k][2];
                    if tmpCall1 < mm {
                        mm := tmpCall1;
                        bestI, bestJ, bestK := i, j, k;
                    }
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    result := mm;
}
// </vc-code>
