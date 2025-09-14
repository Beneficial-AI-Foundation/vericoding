// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Midpoint(low: int, high: int): int {
    low + (high - low) / 2
}

/* helper modified by LLM (iteration 4): Fixed compilation error by removing invalid forall statements from proof blocks */
lemma LemmaMaintainsInvariants(v: array<int>, elem: int, c: int, f: int, mid: int)
    requires 0 <= c <= f + 1 <= v.Length
    requires forall i, j :: 0 <= i < j < v.Length ==> v[i] <= v[j]
    requires forall k :: 0 <= k < c ==> v[k] <= elem
    requires forall k :: f < k < v.Length ==> v[k] > elem
    requires c <= mid <= f
    ensures v[mid] <= elem ==> forall k :: 0 <= k < mid + 1 ==> v[k] <= elem
    ensures v[mid] > elem ==> forall k :: mid < k < v.Length ==> v[k] > elem
{
    if v[mid] <= elem {
        forall k | 0 <= k < mid + 1
            ensures v[k] <= elem
        {
            if k < c {
                // Already given by precondition
            } else if k <= mid {
                // Since the array is sorted, v[k] <= v[mid]
                assert v[k] <= v[mid];
                assert v[mid] <= elem;
                assert v[k] <= elem;
            }
        }
    } else {
        forall k | mid < k < v.Length
            ensures v[k] > elem
        {
            if k <= f {
                // Since the array is sorted, v[mid] <= v[k]
                assert v[mid] <= v[k];
                assert v[mid] > elem;
                assert v[k] > elem;
            } else {
                // Already given by precondition
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method BinarySearchRecursive(v: array<int>, elem: int, c: int, f: int) returns (p: int)
    requires v.Length <= 100000
    requires forall i, j :: 0 <= i < j < v.Length ==> v[i] <= v[j]
    requires 0 <= c <= f + 1 <= v.Length
    requires forall k :: 0 <= k < c ==> v[k] <= elem
    requires forall k :: f < k < v.Length ==> v[k] > elem
    ensures -1 <= p < v.Length
    ensures forall u :: 0 <= u <= p ==> v[u] <= elem
    ensures forall w :: p < w < v.Length ==> v[w] > elem
    decreases f - c + 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Updated comment to reflect iteration 4, no logic change */
    if c > f {
        p := c - 1;
    } else {
        var mid := Midpoint(c, f);
        assert forall i, j :: 0 <= i < j < v.Length ==> v[i] <= v[j];
        if v[mid] <= elem {
            LemmaMaintainsInvariants(v, elem, c, f, mid);
            p := BinarySearchRecursive(v, elem, mid + 1, f);
        } else {
            LemmaMaintainsInvariants(v, elem, c, f, mid);
            p := BinarySearchRecursive(v, elem, c, mid - 1);
        }
    }
}
// </vc-code>
