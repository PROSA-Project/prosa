.PHONY: build upload all backup info

ROCQ_VERSION := ${shell grep ROCQ_VERSION= ../mk-opam-switch.sh  | sed 's|.*=||'}
ROCQ_CORE_VERSION := ${shell grep ROCQ_CORE_VERSION= ../mk-opam-switch.sh  | sed 's|.*=||'}
MATHCOMP_VERSION := ${shell grep MATHCOMP_VERSION= ../mk-opam-switch.sh  | sed 's|.*=||'}

BASE_IMAGE := ${shell head -1 Dockerfile | sed 's|FROM ||g'}

VERSION := ${MATHCOMP_VERSION}-rocq-prover-${ROCQ_VERSION}-rocq-core-${ROCQ_CORE_VERSION}
NAME=mathcomp-for-prosa
IMAGE=${NAME}:${VERSION}

all: info build upload mpi-upload backup

info:
	@echo "Name...: ${NAME}"
	@echo "Version: ${VERSION}"
	@echo "Image..: ${IMAGE}"

build:
	docker pull ${BASE_IMAGE}
	cp ../mk-opam-switch.sh .
	docker build -t ${NAME} .
	rm -f mk-opam-switch.sh

upload:
	docker tag ${NAME} bbbrandenburg/${IMAGE}
	docker push bbbrandenburg/${IMAGE}

mpi-upload:
	@echo "[MAKE] Uploading ${IMAGE} to registry.mpi-sws.org ..."
	docker tag ${NAME} registry.mpi-sws.org/${IMAGE}
	docker push registry.mpi-sws.org/${IMAGE}

backup:
	mkdir -p ${VERSION}
	cp -p Makefile Dockerfile ${VERSION}
