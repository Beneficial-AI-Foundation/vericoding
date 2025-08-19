//ATOM
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)


//ATOM

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)


//ATOM

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{
 match t {
  case Leaf(v) => [ CLf(v) ]
  case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
  case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
 }
}


//IMPL

// Ex 2
method testSerializeWithASingleLeaf()
{
    var leaf := Leaf(42);
    var result := serialise(leaf);
    assert result == [CLf(42)];
}