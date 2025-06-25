struct Queue {
    circularQueue: Vec<i32>,
    rear: usize,
    front: usize,
    counter: usize,
    ghost Content: Seq<i32>,
}

impl Queue {
    spec fn Valid(&self) -> bool {
        0 <= self.counter <= self.circularQueue.len() &&
        0 <= self.front &&
        0 <= self.rear &&
        self.Content == self.circularQueue@
    }

    pub fn new() -> (result: Self)
        ensures(result.circularQueue.len() == 0)
        ensures(result.front == 0 && result.rear == 0)
        ensures(result.Content == Seq::empty())
        ensures(result.counter == 0)
    {
    }

    pub fn insert(&mut self, item: i32)
        requires(self.rear <= self.circularQueue.len())
        ensures((self.front == 0 && self.rear == 0 && self.circularQueue.len() == 1) ==>
            (
                self.Content == seq![item] &&
                self.Content.len() == 1
            ))
    {
    }

    pub fn auxInsertEmptyQueue(&mut self, item: i32)
        requires(self.front == 0 && self.rear == 0 && self.circularQueue.len() == 0)
        ensures(self.circularQueue.len() == 1)
        ensures(self.Content == seq![item])
        ensures(self.Content.len() == 1)
        ensures(self.rear == 1)
        ensures(self.counter == old(self).counter + 1)
        ensures(self.front == 0)
    {
    }

    pub fn auxInsertEndQueue(&mut self, item: i32)
        requires(self.front == 0 && self.rear == self.circularQueue.len() && self.circularQueue.len() >= 1)
        ensures(self.Content == old(self).Content + seq![item])
        ensures(self.Content.len() == old(self).Content.len() + 1)
        ensures(self.front == 0)
        ensures(self.rear == old(self).rear + 1)
        ensures(self.counter == old(self).counter + 1)
    {
    }

    pub fn auxInsertSpaceQueue(&mut self, item: i32)
        requires(self.rear < self.front && self.front < self.circularQueue.len())
        ensures(self.rear == old(self).rear + 1)
        ensures(self.counter == old(self).counter + 1)
        ensures(self.Content == old(self).Content.subrange(0, old(self).rear as int) + seq![item] + old(self).Content.subrange((old(self).rear + 1) as int, old(self).circularQueue.len() as int))
        ensures(self.Content.len() == old(self).Content.len() + 1)
    {
    }

    pub fn auxInsertInitQueue(&mut self, item: i32)
    {
    }

    pub fn auxInsertBetweenQueue(&mut self, item: i32)
    {
    }

    pub fn remove(&mut self) -> (item: i32)
        requires(self.front < self.circularQueue.len())
        requires(self.circularQueue.len() > 0)
        ensures(self.rear <= old(self).Content.len())
        ensures(self.circularQueue.len() > 0)
        ensures(item == old(self).Content[old(self).front as int])
        ensures(self.front == (old(self).front + 1) % self.circularQueue.len())
        ensures(old(self).front < self.rear ==> self.Content == old(self).Content.subrange(old(self).front as int, self.rear as int))
        ensures(old(self).front > self.rear ==> self.Content == old(self).Content.subrange(0, self.rear as int) + old(self).Content.subrange(old(self).front as int, old(self).Content.len() as int))
    {
    }

    pub fn size(&self) -> (size: usize)
        ensures(size == self.counter)
    {
    }

    pub fn isEmpty(&self) -> (isEmpty: bool)
        ensures(isEmpty == true ==> self.counter == 0)
        ensures(isEmpty == false ==> self.counter != 0)
    {
    }

    pub fn contains(&self, item: i32) -> (contains: bool)
        ensures(contains == true ==> self.circularQueue@.contains(item))
        ensures(contains == false ==> !self.circularQueue@.contains(item))
    {
    }
}