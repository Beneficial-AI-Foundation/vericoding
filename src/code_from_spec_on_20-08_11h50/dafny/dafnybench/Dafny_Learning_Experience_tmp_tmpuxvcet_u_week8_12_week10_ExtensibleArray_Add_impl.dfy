class ExtensibleArray<T> {
  var front: array<T>?
  var depot: ExtensibleArray<array<T>>?
  var length: nat
  var M: nat
  
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  
  predicate Valid()
    reads this, Repr
    decreases Repr + {this}
  {
    this in Repr &&
    length == |Elements| &&
    (front != null ==> front in Repr) &&
    (depot != null ==> depot in Repr && depot.Repr <= Repr && this !in depot.Repr) &&
    (front == null ==> length == 0) &&
    (front != null ==> front.Length == 256) &&
    (depot == null ==> M == 0) &&
    (depot != null ==> depot.Valid() && M == 256 * |depot.Elements|) &&
    M <= length <= M + 256 &&
    (forall i :: 0 <= i < M ==> i < |Elements| && Elements[i] == depot.Get(i/256)[i%256]) &&
    (forall i :: M <= i < length ==> i < |Elements| && front != null && Elements[i] == front[i - M])
  }

  <vc-spec>
  constructor ()
    ensures Valid() && fresh(Repr) && Elements == []
  {
    front, depot := null, null;
    length, M := 0, 0;
    Elements, Repr := [], {this};
  }

  function Get(i: int): T
    requires Valid() && 0 <= i < |Elements|
    ensures Get(i) == Elements[i]
    reads Repr
  {
    if M <= i then front[i - M]
    else depot.Get(i/256)[i%256]
  }

// <vc-helpers>
// </vc-helpers>

method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements) + [t]
    decreases |Elements|
// </vc-spec>
// <vc-code>
{
  if front == null {
    // Create a new front array
    front := new T[256];
    Repr := Repr + {front};
    
    // Add element to front
    front[0] := t;
    length := length + 1;
    Elements := Elements + [t];
  } else if length - M == 256 {
    // Front is full, need to move it to depot
    if depot == null {
      depot := new ExtensibleArray<array<T>>();
      Repr := Repr + depot.Repr;
    }
    
    var oldDepotRepr := depot.Repr;
    depot.Add(front);
    Repr := Repr + (depot.Repr - oldDepotRepr);
    M := M + 256;
    
    // Create new front array
    front := new T[256];
    Repr := Repr + {front};
    
    // Add element to new front
    front[0] := t;
    length := length + 1;
    Elements := Elements + [t];
  } else {
    // Add element to existing front
    front[length - M] := t;
    length := length + 1;
    Elements := Elements + [t];
  }
}
// </vc-code>

}