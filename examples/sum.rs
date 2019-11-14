fn main() {
    stack_list::make!(let list = [1, 2, 3, 4]);

    let sum: i32 = list.sum();
    assert_eq!(sum, 10);
}
