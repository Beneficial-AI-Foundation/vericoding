// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
    requires 0 <= b.Length <= a.Length
// </vc-spec>
// <vc-code>
{
    pos := -1;

    if b.Length == 0 {
        return pos;
    }

    var p := 0;

    while p < a.Length
    invariant 0 <= p <= a.Length
    {
        if a.Length - p < b.Length
        {
            return pos;
        }

        if a[p] == b[0] {

                var i := 0;
                    while i < b.Length
                    {
                        if a[i + p] != b[i] {
                            return -1;
                        }
                    i:= i + 1;
                    }
                    pos := p;
                return pos;
        }

        p:= p +1;
    }
}
// </vc-code>
