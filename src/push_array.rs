#[derive(Clone, Copy, Debug)]
pub(crate) struct PushArray<T: Copy, const N: usize>(pub(crate) [T; N]);

macro_rules! impl_push_array {
    ( $( [ $( $copy_index:literal )* ] => $index:literal, )* ) => { $(
        impl<T: Copy> PushArray<T, $index> {
            pub(crate) const fn push(self, value: T) -> PushArray<T, { $index + 1 }> {
                PushArray([ $( self.0[$copy_index], )* value])
            }
        }
    )* };
}

impl_push_array! {
    [] => 0,
    [0] => 1,
    [0 1] => 2,
    [0 1 2] => 3,
    [0 1 2 3] => 4,
    [0 1 2 3 4] => 5,
    [0 1 2 3 4 5] => 6,
    [0 1 2 3 4 5 6] => 7,
    [0 1 2 3 4 5 6 7] => 8,
    [0 1 2 3 4 5 6 7 8] => 9,
    [0 1 2 3 4 5 6 7 8 9] => 10,
    [0 1 2 3 4 5 6 7 8 9 10] => 11,
    [0 1 2 3 4 5 6 7 8 9 10 11] => 12,
    [0 1 2 3 4 5 6 7 8 9 10 11 12] => 13,
    [0 1 2 3 4 5 6 7 8 9 10 11 12 13] => 14,
    [0 1 2 3 4 5 6 7 8 9 10 11 12 13 14] => 15,
    [0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15] => 16,
}
