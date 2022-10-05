.DEFAULT_GOAL := build-sandbox

build-sandbox:
	cd cmd/sandbox; \
	rm sandbox; \
	GOOS=linux GOARCH=amd64 go build; \
	zip sandbox.zip sandbox

update-lambda-function:
	aws lambda update-function-code --function-name lambda-triggered-by-kinesis-data-stream --zip-file fileb://cmd/sandbox/sandbox.zip --publish
