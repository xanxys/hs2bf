
data Test
    =Foo Char
    |Bar
    |Baz

main=case Bar of
    Baz -> Output 'x' Halt
    Bar -> Output 'o' Halt
    Foo x -> Output '*' Halt

