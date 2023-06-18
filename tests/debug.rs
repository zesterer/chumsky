#[cfg(debug_assertions)]
mod debug_asserts {
    use chumsky::prelude::*;

    // TODO panic when left recursive parser is detected
    // #[test]
    // #[should_panic]
    // fn debug_assert_left_recursive() {
    //     recursive(|expr| {
    //         let atom = any::<&str, extra::Default>()
    //             .filter(|c: &char| c.is_alphabetic())
    //             .repeated()
    //             .at_least(1)
    //             .collect();

    //         let sum = expr
    //             .clone()
    //             .then_ignore(just('+'))
    //             .then(expr)
    //             .map(|(a, b)| format!("{}{}", a, b));

    //         sum.or(atom)
    //     })
    //     .then_ignore(end())
    //     .parse("a+b+c");
    // }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn debug_assert_collect() {
        empty::<&str, extra::Default>()
            .to(())
            .repeated()
            .collect::<()>()
            .parse("a+b+c")
            .unwrap();
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn debug_assert_separated_by() {
        empty::<&str, extra::Default>()
            .to(())
            .separated_by(empty())
            .collect::<()>()
            .parse("a+b+c");
    }

    #[test]
    fn debug_assert_separated_by2() {
        assert_eq!(
            empty::<&str, extra::Default>()
                .to(())
                .separated_by(just(','))
                .count()
                .parse(",")
                .unwrap(),
            2
        );
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn debug_assert_foldl() {
        assert_eq!(
            empty::<&str, extra::Default>()
                .to(1)
                .foldl(empty().repeated(), |n, ()| n + 1)
                .parse("a+b+c")
                .unwrap(),
            3
        );
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn debug_assert_foldl_with_state() {
        let mut state = 100;
        empty::<&str, extra::Full<EmptyErr, i32, ()>>()
            .foldl_with_state(empty().to(()).repeated(), |_, _, _| ())
            .parse_with_state("a+b+c", &mut state);
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn debug_assert_foldr() {
        empty::<&str, extra::Default>()
            .to(())
            .repeated()
            .foldr(empty(), |_, _| ())
            .parse("a+b+c");
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn debug_assert_foldr_with_state() {
        empty::<&str, extra::Default>()
            .to(())
            .repeated()
            .foldr_with_state(empty(), |_, _, _| ())
            .parse_with_state("a+b+c", &mut ());
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn debug_assert_repeated() {
        empty::<&str, extra::Default>()
            .to(())
            .repeated()
            .parse("a+b+c");
    }

    // TODO what about IterConfigure and TryIterConfigure?
}
