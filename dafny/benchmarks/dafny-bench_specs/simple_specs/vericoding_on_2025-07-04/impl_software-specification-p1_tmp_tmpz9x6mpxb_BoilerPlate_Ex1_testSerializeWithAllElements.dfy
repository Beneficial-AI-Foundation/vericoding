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

method testSerializeWithAllElements()
{
    // Test with a simple leaf
    var leaf := Leaf(1);
    var leafSerialized := serialise(leaf);
    assert leafSerialized == [CLf(1)];
    
    // Test with a single node
    var singleNode := SingleNode(2, Leaf(3));
    var singleSerialized := serialise(singleNode);
    assert singleSerialized == [CLf(3), CSNd(2)];
    
    // Test with a double node
    var doubleNode := DoubleNode(4, Leaf(5), Leaf(6));
    var doubleSerialized := serialise(doubleNode);
    assert doubleSerialized == [CLf(6), CLf(5), CDNd(4)];
    
    // Test with a more complex tree using all elements
    var complexTree := DoubleNode(1, 
                                 SingleNode(2, Leaf(3)), 
                                 DoubleNode(4, Leaf(5), Leaf(6)));
    var complexSerialized := serialise(complexTree);
    assert complexSerialized == [CLf(6), CLf(5), CDNd(4), CLf(3), CSNd(2), CDNd(1)];
}