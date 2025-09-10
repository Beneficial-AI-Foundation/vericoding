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
lemma WinnerValid(a: char, b: char)
    requires validRPSChar(a) && validRPSChar(b)
    ensures validRPSChar(winner(a,b))
{
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') {
        // winner is b
    } else {
        // winner is a
    }
}

lemma AppendValidChar(s: string, c: char)
    requires validRPSString(s)
    requires validRPSChar(c)
    ensures validRPSString(s + c)
{
    forall j | 0 <= j < |s| + 1
        ensures validRPSChar((s+c)[j])
    {
        if j < |s| {
            assert (s+c)[j] == s[j];
        } else {
            assert j == |s|;
            assert (s+c)[j] == c;
        }
    }
}
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
                var oldNext := next;
                var w := winner(current[i], current[i+1]);
                next := oldNext + w;
                WinnerValid(current[i], current[i+1]);
                AppendValidChar(oldNext, w);
                i := i + 2;
            } else {
                var oldNext := next;
                next := oldNext + current[i];
                AppendValidChar(oldNext, current[i]);
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

