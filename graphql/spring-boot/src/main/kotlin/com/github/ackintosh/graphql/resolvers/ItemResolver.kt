package com.github.ackintosh.graphql.resolvers

import com.coxautodev.graphql.tools.GraphQLResolver
import com.github.ackintosh.graphql.types.Item
import com.github.ackintosh.graphql.types.Recommend
import org.springframework.stereotype.Component

@Component
class ItemResolver: GraphQLResolver<Recommend> {
    private val recommendToItems = mapOf(
            1 to listOf(Item(1, "トートバッグ"), Item(2, "クッションケース")),
            2 to listOf(Item(3, "折りたたみテーブル"), Item(4, "ホワイトボード"))
    )

    fun items(recommend: Recommend) = recommendToItems[recommend.id]
}