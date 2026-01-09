FROM archlinux:base-devel

SHELL ["/bin/bash", "--login", "-o", "pipefail", "-c"]

RUN set -x \
    && echo "Installing packages..." \
    && pacman -Sy --noconfirm python uv opam rsync git \
    && echo "Creating user..." \
    && useradd -m -u 21408 -g users rocq

WORKDIR /home/rocq
USER rocq

ADD mk-opam-switch.sh /home/rocq/
RUN set -x \
    && opam init --auto-setup --yes --bare --disable-sandboxing \
    && /home/rocq/mk-opam-switch.sh \
    && eval $(opam env) \
    && opam clean -a -c -s --logs \
    && rm /home/rocq/mk-opam-switch.sh \
    && opam config list && opam list

ENTRYPOINT ["opam", "exec", "--"]

CMD ["/bin/bash", "--login"]

LABEL maintainer="bbb@mpi-sws.org"
