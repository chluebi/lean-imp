FROM debian
USER root
# install prerequisites
RUN apt-get update && apt-get install curl git -y && apt-get clean

# necessary for mathlib
RUN apt-get install npm -y


# create a non-root user
RUN useradd -m lean

USER lean
WORKDIR /home/lean

SHELL ["/bin/bash", "-c"]
# set the entrypoint to be a login shell, so everything is on the PATH
ENTRYPOINT ["/bin/bash", "-l"]

# make sure binaries are available even in non-login shells
ENV PATH="/home/lean/.elan/bin:/home/lean/.local/bin:$PATH"

# install elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none && \
    . ~/.profile && \
    elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib/master/leanpkg.toml | grep lean_version | awk -F'"' '{print $2}') && \
    elan default stable

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true

