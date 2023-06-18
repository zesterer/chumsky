import turtle

board = turtle.Turtle(
    foo,
    bar,
    baz,
)

for i in range(6):
    board.forward(50)
    if i % 2 == 0:
        board.right(144)
    else:
        board.left(72)

turtle.done()
