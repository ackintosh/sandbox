package docker

import (
	"context"
	"fmt"
	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/container"
	"github.com/docker/docker/api/types/network"
	"github.com/docker/docker/client"
	"github.com/docker/go-connections/nat"
	specs "github.com/opencontainers/image-spec/specs-go/v1"
	"testing"
)

func TestContainerList(t *testing.T) {
	cli, err := client.NewClientWithOpts()
	if err != nil {
		panic(err)
	}

	containers, err := cli.ContainerList(context.Background(), types.ContainerListOptions{})
	if err != nil {
		panic(err)
	}

	for _, container := range containers {
		fmt.Printf("%s %s\n", container.ID[:10], container.Image)
	}
}

func TestContainerCreate(t *testing.T) {
	cli, err := client.NewClientWithOpts()
	if err != nil {
		panic(err)
	}

	onBuild := []string{"RUN echo 123 > /tmp/test"}
	_, exposed, _ := nat.ParsePortSpecs([]string{"30000:3000"})
	res, err := cli.ContainerCreate(
		context.Background(),
		&container.Config{
			Image:   "grafana/grafana",
			OnBuild: onBuild,
		},
		&container.HostConfig{
			PortBindings: exposed,
		},
		&network.NetworkingConfig{},
		&specs.Platform{},
		"sandbox-docker-test-container",
	)
	if err != nil {
		panic(err)
	}

	fmt.Printf("Container ID: %s\n", res.ID)
}
