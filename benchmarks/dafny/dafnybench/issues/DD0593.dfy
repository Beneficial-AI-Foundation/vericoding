// <vc-preamble>
// Examples used in paper:
//   Specification and Verification of Object-Oriented Software
// by K. Rustan M. Leino
// link of the paper:
//   http://leino.science/papers/krml190.pdf

// Figure 0. An example linked-list program written in Dafny.
class Data { }

class Node {
  var list: seq<Data>;
  var footprint: set<Node>;

  var data: Data;
  var next: Node?;

  function Valid(): bool
    reads this, footprint
  {
    this in footprint &&
    (next == null ==> list  == [data]) &&
    (next != null ==> next in footprint &&
                      next.footprint <= footprint &&
                      !(this in next.footprint) &&
                      list == [data] + next.list &&
                      next.Valid())
  }

  constructor(d: Data)
    ensures Valid() && fresh(footprint - {this})
    ensures list == [d]
  {
    data := d;
    next := null;
    list := [d];
    footprint := {this};
  }
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SkipHead() returns (r: Node?)
    requires Valid()
    ensures r == null ==> |list| == 1
    ensures r != null ==> r.Valid() && r.footprint <= footprint
// </vc-spec>
// <vc-code>
{
    return next;
}
// </vc-code>

// Figure 1: The Node.ReverseInPlace method,
  //     which performs an in situ list reversal.
}