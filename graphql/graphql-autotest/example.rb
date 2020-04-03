require 'graphql/autotest'

fields = GraphQL::Autotest::QueryGenerator.from_file(path: './schema.graphql')

p fields

# Print all generated queries
fields.each do |field|
  puts field.to_query
end
