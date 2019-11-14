/// Lists all dividers of the given number (except for 1, which would always be there).
fn all_dividers(n: u32) -> impl Iterator<Item = u32> {
    (2..=n / 2).into_iter().filter(move |i| n % i == 0)
}

fn print_dividers(n: u32) {
    // We will use a context to keep the list of child IDs.
    // This way, on each row we can print the entire history as a prefix.
    fn print_prefix<'a>(context: &stack_list::Node<'a, u32>) {
        context.for_each_rev(|parent| {
            let color_id = parent % 6;
            // find a unique color
            print!("\x1B[{}m▉\x1B[0m", 31 + color_id);
        });
    }

    fn print_dividers_inner<'a>(n: u32, context: &stack_list::Node<'a, u32>) {
        print_prefix(context);
        println!("{}", n);
        for divider in all_dividers(n) {
            print_dividers_inner(divider, &context.prepend(divider));
        }
    }

    print_dividers_inner(n, &stack_list::Node::new());
}

fn main() {
    print_dividers(102);
}
