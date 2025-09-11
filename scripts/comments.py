def comment_ranges(src):
    "Identify comments in Gallina files (i.e., Rocq's .v files)."

    def cur_is(i, c):
        return src[i] == c

    def next_is(i, c):
        if i + 1 < len(src):
            return src[i + 1] == c
        else:
            return False

    in_comment = 0
    comment_start = None

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
