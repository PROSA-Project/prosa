from bisect import bisect
from collections.abc import Iterable, Iterator
from functools import cached_property


def comment_ranges(src) -> Iterator[tuple[int, int]]:
    "Identify comments in Gallina files (i.e., Rocq's .v files)."

    def cur_is(i, c):
        return src[i] == c

    def next_is(i, c):
        if i + 1 < len(src):
            return src[i + 1] == c
        else:
            return False

    in_comment = 0
    comment_start = 0

    # limitation: doesn't do anything smart about nested comments for now
    for i in range(len(src)):
        assert in_comment >= 0
        # comment starting?
        if cur_is(i, "(") and next_is(i, "*"):
            in_comment += 1
            if in_comment == 1:
                if next_is(i + 1, "*"):
                    comment_start = i + 3
                else:
                    comment_start = i + 2
        # comment ending?
        elif cur_is(i, "*") and next_is(i, ")"):
            in_comment -= 1
            if in_comment == 0:
                yield (comment_start, i)


def line_ranges(src) -> Iterator[tuple[int, int]]:
    "Yield a list of offset pairs indicating all lines in the input"
    last = 0
    _line_ranges = []
    for i, c in enumerate(src):
        if c == "\n":
            yield (last, i + 1)
            last = i + 1
    if last < len(src):
        yield (last, len(src))


class Ranges:
    def __init__(self, ranges: Iterable[tuple[int, int]]):
        self.ranges = tuple(ranges)

    def lookup(self, pos: int | tuple[int, int]) -> tuple[int, tuple[int, int]] | None:
        s = pos[0] if isinstance(pos, tuple) else pos
        e = pos[1] if isinstance(pos, tuple) else pos + 1
        x = bisect(self.ranges, s, key=lambda r: r[1])
        for i, r in enumerate(self.ranges[x:]):
            if r[0] <= s < r[1] and r[0] < e <= r[1]:
                return (i + x), r
            if s >= r[1]:
                break
        return None

    def __iter__(self) -> Iterator[tuple[int, int]]:
        return iter(self.ranges)

    def __getitem__(self, pos: int | tuple[int, int]) -> tuple[int, int] | None:
        where = self.lookup(pos)
        if where is not None:
            return where[1]
        else:
            return

    def __contains__(self, pos: int | tuple[int, int]) -> bool:
        return self.lookup(pos) is not None


class Comments:
    def __init__(self, src):
        self.src = src

    @cached_property
    def ranges(self) -> Ranges:
        return Ranges(comment_ranges(self.src))

    def __iterator__(self) -> Iterator[str]:
        return (self.src[s:e] for s, e in self.ranges)

    def __contains__(self, pos):
        return pos in self.ranges


class LineNumbers:
    def __init__(self, src):
        self.src = src

    @cached_property
    def ranges(self) -> Ranges:
        return Ranges(line_ranges(self.src))

    def lines(self) -> Iterator[str]:
        return (self.src[s:e] for s, e in self.ranges)

    @cached_property
    def _lines(self) -> list[str]:
        return list(self.lines())

    def line(self, line_number: int) -> str:
        return self._lines[line_number - 1]

    def line_containing(self, pos: int) -> tuple[int, tuple[int, int]]:
        where = self.ranges.lookup(pos)
        if where is not None:
            return where
        else:
            raise IndexError(f"{pos} is not a valid file offset")

    def line_number_for_offset(self, pos: int) -> int:
        where = self.line_containing(pos)
        return where[0] + 1

    def line_for_offset(self, pos: int) -> str:
        where = self.line_containing(pos)
        return self.src[where[1][0] : where[1][1]]

    def line_start_for_offset(self, pos: int) -> int:
        return self.line_containing(pos)[1][0]

    def offset_within_line(self, pos: int) -> int:
        return pos - self.line_start_for_offset(pos)

    def __getitem__(self, pos: int) -> int:
        return self.line_number_for_offset(pos)

    def __contains__(self, pos: int) -> bool:
        return pos in self.ranges
