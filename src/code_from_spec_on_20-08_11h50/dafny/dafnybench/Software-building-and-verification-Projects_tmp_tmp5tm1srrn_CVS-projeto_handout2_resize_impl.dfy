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

// <vc-spec>
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


  function {:axiom} hash(key:K) : int
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

// <vc-helpers>
ghost predicate all_data_rehashed(oldData: array<List<(K,V)>>, newData: array<List<(K,V)>>, processed: int, oldSize: int, newSize: int)
  reads oldData, newData
  requires 0 <= processed <= oldSize
  requires oldData.Length == oldSize
  requires newData.Length == newSize
  requires newSize > 0
{
  forall k,v :: (exists j :: 0 <= j < processed && mem((k,v), oldData[j])) ==>
    mem((k,v), newData[bucket(k, newSize)])
}

lemma PreserveElemsHelper(oldData: array<List<(K,V)>>, newData: array<List<(K,V)>>, oldSize: int, newSize: int, oldElems: map<K,Option<V>>)
  requires oldData.Length == oldSize > 0
  requires newData.Length == newSize > 0
  requires forall k,v :: (k in oldElems && oldElems[k] == Some(v)) <==> mem((k,v), oldData[bucket(k, oldSize)])
  requires all_data_rehashed(oldData, newData, oldSize, oldSize, newSize)
  ensures forall k :: k in oldElems && oldElems[k].Some? ==> (exists j :: 0 <= j < oldSize && mem((k, oldElems[k].elem), oldData[j]))
  ensures forall k :: k in oldElems && oldElems[k].Some? ==> mem((k, oldElems[k].elem), newData[bucket(k, newSize)])
{
  forall k | k in oldElems && oldElems[k].Some?
  ensures mem((k, oldElems[k].elem), newData[bucket(k, newSize)])
  {
    var v := oldElems[k].elem;
    assert mem((k,v), oldData[bucket(k, oldSize)]);
    var j := bucket(k, oldSize);
    assert 0 <= j < oldSize;
    assert mem((k,v), oldData[j]);
    assert all_data_rehashed(oldData, newData, oldSize, oldSize, newSize);
    assert mem((k,v), newData[bucket(k, newSize)]);
  }
}

ghost predicate bucket_consistent(oldData: array<List<(K,V)>>, oldSize: int)
  reads oldData
  requires oldData.Length == oldSize > 0
{
  forall i :: 0 <= i < oldSize ==> 
    forall k,v :: mem((k,v), oldData[i]) ==> bucket(k, oldSize) == i
}

lemma EstablishBucketConsistency(data: array<List<(K,V)>>)
  requires data.Length > 0
  requires forall i :: 0 <= i < data.Length ==> valid_hash(data, i)
  ensures bucket_consistent(data, data.Length)
{
  forall i | 0 <= i < data.Length
  ensures forall k,v :: mem((k,v), data[i]) ==> bucket(k, data.Length) == i
  {
    forall k,v | mem((k,v), data[i])
    ensures bucket(k, data.Length) == i
    {
      assert valid_hash(data, i);
      assert bucket(k, data.Length) == i;
    }
  }
}
// </vc-helpers>

method resize()
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures forall key :: key in old(elems) ==> key in elems
    ensures forall k,v :: k in old(elems) && old(elems)[k] == Some(v) ==> k in elems && elems[k] == Some(v)
    modifies Repr
// </vc-spec>
// <vc-code>
{
  var oldData := data;
  var oldSize := data.Length;
  var newSize := 2 * oldSize;
  var oldElems := elems;
  
  assert oldSize > 0;
  assert newSize > 0;
  
  var newData := new List<(K,V)>[newSize](i => Nil);
  
  // Establish bucket consistency from RepInv
  EstablishBucketConsistency(oldData);
  assert bucket_consistent(oldData, oldSize);
  
  var i := 0;
  while i < oldSize
    invariant 0 <= i <= oldSize
    invariant newData.Length == newSize
    invariant oldData.Length == oldSize
    invariant newData != oldData
    invariant newSize > 0
    invariant oldSize > 0
    invariant newSize == 2 * oldSize
    invariant forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    invariant all_data_rehashed(oldData, newData, i, oldSize, newSize)
    invariant bucket_consistent(oldData, oldSize)
    invariant forall k,v :: (exists j :: i <= j < oldSize && mem((k,v), oldData[j])) ==>
                            !mem((k,v), newData[bucket(k, newSize)])
  {
    assert 0 <= i < oldSize;
    assert forall k,v :: mem((k,v), oldData[i]) ==> bucket(k, oldSize) == i;
    rehash(oldData[i], newData, i, oldSize, newSize);
    i := i + 1;
  }
  
  // Establish precondition for PreserveElemsHelper
  assert forall k,v :: (k in oldElems && oldElems[k] == Some(v)) <==> mem((k,v), oldData[bucket(k, oldSize)]) by {
    forall k,v 
    ensures (k in oldElems && oldElems[k] == Some(v)) <==> mem((k,v), oldData[bucket(k, oldSize)])
    {
      assert valid_data(k,v,oldElems,oldData);
    }
  }
  
  // Apply helper lemma
  PreserveElemsHelper(oldData, newData, oldSize, newSize, oldElems);
  
  // Update data structure
  data := newData;
  Repr := {this, data};
  
  // Prove postconditions
  forall k | k in oldElems
  ensures k in elems
  ensures elems[k] == oldElems[k]
  {
    if oldElems[k].Some? {
      var v := oldElems[k].elem;
      assert mem((k,v), newData[bucket(k, newSize)]);
      assert data == newData;
      assert data.Length == newSize;
      assert bucket(k, data.Length) == bucket(k, newSize);
      assert mem((k,v), data[bucket(k, data.Length)]);
      assert valid_data(k, v, elems, data);
      assert k in elems && elems[k] == Some(v);
    } else {
      assert oldElems[k] == None;
      assert forall v :: !mem((k,v), oldData[bucket(k, oldSize)]);
      assert forall v :: !mem((k,v), newData[bucket(k, newSize)]);
      assert forall v :: !mem((k,v), data[bucket(k, data.Length)]);
      assert !(k in elems) || elems[k] == None;
    }
  }
}
// </vc-code>

method rehash(l: List<(K,V)>, newData: array<List<(K,V)>>,i: int, oldSize: int, newSize: int)
    requires newData != data
    requires 0 < oldSize == data.Length
    requires newData.Length == 2 * oldSize == newSize
    requires forall k,v :: mem((k,v), l) ==> bucket(k, oldSize) == i
    requires forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    requires forall k,v :: (
                           if 0 <= bucket(k, oldSize) < i then
                             valid_data(k,v,elems,newData)
                           else if bucket(k, oldSize) == i then
                             ((k in elems && elems[k] == Some(v))
                              <==> mem((k,v), l) || mem((k,v),newData[bucket(k, newSize)]))
                           else
                             !mem((k,v),newData[bucket(k, newSize)]))
    ensures forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    ensures forall k,v ::
              (if 0 <= bucket(k, oldSize) <= i then
                valid_data(k,v,elems,newData)
              else
                !mem((k,v),newData[bucket(k, newSize)]))
    modifies newData
    decreases l
  {
    match l {
      case Nil => return;
      case Cons((k,v), r) => {
        var b := bucket(k, newSize);
        newData[b] := Cons((k,v), newData[b]);
        rehash(r, newData, i, oldSize, newSize);
      }
    }
  }





}