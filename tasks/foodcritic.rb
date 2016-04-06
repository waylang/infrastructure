require 'foodcritic'

FoodCritic::Rake::LintTask.new do |foodcritic|
  foodcritic.options[:tags] = %w(correctness ~FC055 ~FC056)
end

task default: :foodcritic
