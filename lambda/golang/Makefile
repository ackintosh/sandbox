build:
	GOOS=linux GOARCH=amd64 go build -v -o main .

zip: build
	zip main.zip ./main
