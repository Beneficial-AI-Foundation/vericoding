// <vc-preamble>
datatype List<T> = Nil | Cons(head:T,tail:List<T>)
datatype Option<T> = None | Some(elem:T)

ghost function mem<T>(x:T,l:List<T>) : bool {
  match l {
    case Nil => false
    case Cons(y,xs) => x==y || mem(x,xs)
  }
}

ghost function length<T>(l:List<T>) : int {
  match l {
    case Nil => 0
    case Cons(_,xs) => 1 + length(xs)
  }
}

function list_find<K(==),V(!new)>(k:K,l:List<(K,V)>) : Option<V>
  ensures match list_find(k,l) {
            case None => forall v :: !mem((k,v),l)
            case Some(v) => mem((k,v),l)
          }
  decreases l
{
  match l {
    case Nil => None
    case Cons((k',v),xs) => if k==k' then Some(v) else list_find(k,xs)
  }
}

function list_remove<K(==,!new),V(!new)>(k:K, l:List<(K,V)>) : List<(K,V)>
  decreases l
  ensures forall k',v :: mem((k',v),list_remove(k,l)) <==> (mem((k',v),l) && k != k')
{
  match l {
    case Nil => Nil
    case Cons((k',v),xs) => if k==k' then list_remove(k,xs) else
    Cons((k',v),list_remove(k,xs))
  }
}


class Hashtable<K(==,!new),V(!new)> {
  var size : int
  var data : array<List<(K,V)>>

  ghost var Repr : set<object>
  ghost var elems : map<K,Option<V>>

  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && data in Repr && data.Length > 0 &&
    (forall i :: 0 <= i < data.Length ==> valid_hash(data, i)) &&
    (forall k,v :: valid_data(k,v,elems,data))
  }

  ghost predicate valid_hash(data: array<List<(K,V)>>, i: int)
    requires 0 <= i < data.Length
    reads data
  {
    forall k,v :: mem((k,v), data[i]) ==> (bucket(k,data.Length) == i)
  }


  ghost predicate valid_data(k: K,v: V,elems: map<K, Option<V>>, data: array<List<(K,V)>>)
    reads this, Repr, data
    requires data.Length > 0
  {
    (k in elems && elems[k] == Some(v)) <==> mem((k,v), data[bucket(k, data.Length)])
  }


  function hash(key:K) : int
    ensures hash(key) >= 0

  function bucket(k: K, n: int) : int
    requires n > 0
    ensures 0 <= bucket(k, n) < n
  {
    hash(k) % n
  }

  constructor(n:int)
    requires n > 0
    ensures RepInv()
    ensures fresh(Repr-{this})
    ensures elems == map[]
    ensures size == 0
  {
    size := 0;
    data := new List<(K,V)>[n](i => Nil);
    Repr := {this, data};
    elems := map[];
  }
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method clear()
    requires RepInv()
    ensures RepInv()
    ensures elems == map[]
    ensures fresh(Repr - old(Repr))
    modifies Repr
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < data.Length
      invariant 0 <= i <= data.Length
      invariant forall j :: 0 <= j < i ==> data[j] == Nil
      modifies data
    {
      data[i] := Nil;
      i := i + 1;
    }
    size := 0;
    elems := map[];
}
// </vc-code>

}