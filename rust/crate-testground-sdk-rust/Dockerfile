FROM rust:1.57-bullseye as builder
WORKDIR /usr/src/sdk-rust
COPY . .
RUN cd plan && cargo build

FROM debian:bullseye-slim
COPY --from=builder /usr/src/sdk-rust/plan/target/debug/crate-testground-sdk-rust /usr/local/bin/sandbox
EXPOSE 6060
ENTRYPOINT [ "sandbox"]