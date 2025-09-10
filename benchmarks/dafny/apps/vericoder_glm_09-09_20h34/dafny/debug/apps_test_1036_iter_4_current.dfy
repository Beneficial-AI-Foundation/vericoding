function winner(a: char, b: char): char
{
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') then b else a
}

predicate validRPSChar(c: char)
{
    c == 'R' || c == 'P' || c == 'S'
}

predicate validRPSString(s: string)
{
    forall i :: 0 <= i < |s| ==> validRPSChar(s[i])
}

predicate ValidInput(n: int, k: int, s: string)
{
    n > 0 && k >= 0 && |s| == n && validRPSString(s)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: char)
    requires ValidInput(n, k, s)
    ensures validRPSChar(result)
// </vc-spec>
// <vc-code>
{
    var current := s;
    var current_n := n;
    var round := 0;

    while round < k && current_n > 1
        invariant round <= k
        invariant current_n >= 1
        invariant |current| == current_n
        invariant validRPSString(current)
    {
        var next := "";
        var i := 0;
        while i < current_n
            invariant 0 <= i <= current_n
            invariant |next| == (i+1)/2
            invariant validRPSString(next)
        {
            if i + 1 < current_n {
                var w := winner(current[i], current[i+1]);
                next := next + w;
                i := i + 2;
            } else {
                next := next + current[i];
                i := i + 1;
            }
        }
        current := next;
        current_n := |next|;
        round := round + 1;
    }

    result := current[0];
}
// </vc-code>

