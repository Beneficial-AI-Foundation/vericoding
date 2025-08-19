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

method testSerializeNullValues()
{
    var leaf := Leaf(0);
    var result := serialise(leaf);
    assert result == [CLf(0)];
    
    var singleNode := SingleNode(1, Leaf(2));
    var result2 := serialise(singleNode);
    assert result2 == [CLf(2), CSNd(1)];
    
    var doubleNode := DoubleNode(3, Leaf(4), Leaf(5));
    var result3 := serialise(doubleNode);
    assert result3 == [CLf(5), CLf(4), CDNd(3)];
}