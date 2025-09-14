// <vc-preamble>
predicate IsSubrangeAt(main: seq<int>, sub: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && sub == main[i..i+|sub|]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSubArray(main: array<int>, sub: array<int>) returns (result: bool)
    ensures result == (exists k :: 0 <= k <= (main.Length - sub.Length) && IsSubrangeAt(main[..], sub[..], k))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added pre-check for sub.length > main.length to fix loop invariant */
    if sub.Length > main.Length {
        result := false;
        return;
    }

    result := false;
    var i := 0;
    while i <= main.Length - sub.Length
        invariant 0 <= i <= main.Length - sub.Length + 1
        invariant sub.Length <= main.Length
        invariant result <==> (exists k :: 0 <= k < i && IsSubrangeAt(main[..], sub[..], k))
    {
        if IsSubrangeAt(main[..], sub[..], i) {
            result := true;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
