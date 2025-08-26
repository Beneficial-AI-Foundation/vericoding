// <vc-helpers>
type T

class MemoryReader {
    var mem_: array<T>
// </vc-helpers>

// <vc-spec>
method read(off : int) returns (r : T)
        requires 0 <= off < mem_.Length
// </vc-spec>

// <vc-code>
{
    r := mem_[off];
}
// </vc-code>

}