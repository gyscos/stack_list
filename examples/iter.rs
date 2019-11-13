fn main() {
    stack_list::make!(let l = [1, 2, 3, 4]);

    let v: Vec<_> = dbg!(l.iter().copied().collect());

    stack_list::Node::from_iterator(v.iter(), |node| {
        println!("{:?}", node.skip(2));
    });
}
