FROM archlinux:base-devel

RUN set -x \
    && echo "Installing packages..." \
    && pacman -Sy --noconfirm python uv opam rsync \
    && echo "Creating user..." \
    && useradd -m -u 21408 -g users rocq

WORKDIR /home/rocq
USER rocq

ADD mk-opam-switch.sh /home/rocq/
RUN set -x \
    && opam init --disable-sandboxing \
    && /home/rocq/mk-opam-switch.sh \
    && eval $(opam env) \
    && opam clean -a -c -s --logs \
    && rm /home/rocq/mk-opam-switch.sh \
    && opam config list && opam list
