package com.github.ackintosh.graphql

import com.github.ackintosh.graphql.dataloader.ItemDataLoader
import com.github.ackintosh.graphql.type.Item
import graphql.kickstart.execution.context.DefaultGraphQLContext
import graphql.kickstart.execution.context.GraphQLContext
import graphql.servlet.context.DefaultGraphQLServletContext
import graphql.servlet.context.DefaultGraphQLWebSocketContext
import graphql.servlet.context.GraphQLServletContextBuilder
import org.dataloader.DataLoader
import org.dataloader.DataLoaderRegistry
import org.springframework.stereotype.Component
import javax.servlet.http.HttpServletRequest
import javax.servlet.http.HttpServletResponse
import javax.websocket.Session
import javax.websocket.server.HandshakeRequest

@Component
class CustomGraphQLContextBuilder(
        val itemDataLoader: ItemDataLoader
) : GraphQLServletContextBuilder {
    override fun build(req: HttpServletRequest?, res: HttpServletResponse?): GraphQLContext =
            DefaultGraphQLServletContext.createServletContext(buildDataLoaderRegistry(), null)
                    .with(req)
                    .with(res)
                    .build()

    override fun build(session: Session?, request: HandshakeRequest?): GraphQLContext =
            DefaultGraphQLWebSocketContext.createWebSocketContext(buildDataLoaderRegistry(), null)
                    .with(session)
                    .with(request)
                    .build()

    override fun build(): GraphQLContext = DefaultGraphQLContext(buildDataLoaderRegistry(), null)

    private fun buildDataLoaderRegistry(): DataLoaderRegistry {
        val registry = DataLoaderRegistry();
        registry.register("itemDataLoader", DataLoader.newDataLoader(itemDataLoader.loader()))
        return registry
    }
}